/* grep.c - main driver file for grep.
 Copyright (C) 1992, 1997-2002, 2004-2016 Free Software Foundation, Inc.
 
 This program is free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 3, or (at your option)
 any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston, MA
 02110-1301, USA.  */

/* Written July 1992 by Mike Haertel.  */

#include <config.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <wchar.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <pthread.h>
#include "system.h"

#include "argmatch.h"
#include "c-ctype.h"
#include "closeout.h"
#include "colorize.h"
#include "error.h"
#include "exclude.h"
#include "exitfail.h"
#include "fcntl-safer.h"
#include "fts_.h"
#include "getopt.h"
#include "getprogname.h"
#include "grep.h"
#include "intprops.h"
#include "propername.h"
#include "quote.h"
#include "safe-read.h"
#include "search.h"
#include "version-etc.h"
#include "xalloc.h"
#include "xstrtol.h"

#define SEP_CHAR_SELECTED ':'
#define SEP_CHAR_REJECTED '-'
#define SEP_STR_GROUP    "--"

#define AUTHORS \
proper_name ("Mike Haertel"), \
_("others, see <http://git.sv.gnu.org/cgit/grep.git/tree/AUTHORS>")

/* When stdout is connected to a regular file, save its stat
 information here, so that we can automatically skip it, thus
 avoiding a potential (racy) infinite loop.  */
static struct stat out_stat;

/* if non-zero, display usage information and exit */
static int show_help;

/* Print the version on standard output and exit.  */
static bool show_version;

/* Suppress diagnostics for nonexistent or unreadable files.  */
static bool suppress_errors;

/* If nonzero, use color markers.  */
static int color_option;

/* Show only the part of a line matching the expression. */
static bool only_matching;

/* If nonzero, make sure first content char in a line is on a tab stop. */
static bool align_tabs;

/* Use multithreading on the file granularity */
static bool parallel = false;
static bool parallel_explicitly_specified = false;
int num_threads;

/* See below */
struct FL_pair
{
  char const *filename;
  size_t lineno;
};

/* A list of lineno,filename pairs corresponding to -f FILENAME
 arguments. Since we store the concatenation of all patterns in
 a single array, KEYS, be they from the command line via "-e PAT"
 or read from one or more -f-specified FILENAMES.  Given this
 invocation, grep -f <(seq 5) -f <(seq 2) -f <(seq 3) FILE, there
 will be three entries in LF_PAIR: {1, x} {6, y} {8, z}, where
 x, y and z are just place-holders for shell-generated names.  */
static struct FL_pair *fl_pair;
static size_t n_fl_pair_slots;
/* Count not only -f-specified files, but also individual -e operands
 and any command-line argument that serves as a regular expression.  */
static size_t n_pattern_files;

/* Given the concatenation of all patterns, one per line, be they
 specified via -e, a lone command-line argument or -f, this is the
 number of the first line of each entity, in that concatenation.
 It is advanced by fl_add and, when needed, used in pattern_file_name
 to derive a file-relative line number.  */
static uintmax_t patfile_lineno = 1;

/* Return the number of newline bytes in BUF starting at offset BEG
 and up to and not including offset END.  */
static size_t _GL_ATTRIBUTE_PURE
count_nl_bytes (char const *buf, size_t beg, size_t end)
{
  char const *p = buf + beg;
  char const *end_p = buf + end;
  uintmax_t n = 0;
  while (true)
  {
    p = memchr (p, '\n', end_p - p);
    if (!p)
      break;
    p++;
    n++;
  }
  return n;
}

/* Append a FILENAME,line-number pair to FL_PAIR.  The line number we save
 with FILENAME is the initial value of the global PATFILE_LINENO.
 PATFILE_LINENO is then incremented by the number of newlines in BUF
 from offset BEG up to but not including offset END.  */
static void
fl_add (char const *buf, size_t beg, size_t end, char const *filename)
{
  if (n_fl_pair_slots <= n_pattern_files)
    fl_pair = x2nrealloc (fl_pair, &n_fl_pair_slots, sizeof *fl_pair);
  
  fl_pair[n_pattern_files].lineno = patfile_lineno;
  fl_pair[n_pattern_files].filename = filename;
  n_pattern_files++;
  patfile_lineno += count_nl_bytes (buf, beg, end);
}

/* Map the line number, LINENO, of one of the input patterns to the
 name of the file from which it came.  If it was read from stdin
 or if it was specified on the command line, return "-".  */
char const * _GL_ATTRIBUTE_PURE
pattern_file_name (size_t lineno, size_t *new_lineno)
{
  size_t i;
  for (i = 1; i < n_pattern_files; i++)
  {
    if (lineno < fl_pair[i].lineno)
      break;
  }
  
  *new_lineno = lineno - fl_pair[i - 1].lineno + 1;
  return fl_pair[i - 1].filename;
}

#if HAVE_ASAN
/* Record the starting address and length of the sole poisoned region,
 so that we can unpoison it later, just before each following read.  */
static void const *poison_buf;
static size_t poison_len;

static void
clear_asan_poison (void)
{
  if (poison_buf)
    __asan_unpoison_memory_region (poison_buf, poison_len);
}

static void
asan_poison (void const *addr, size_t size)
{
  poison_buf = addr;
  poison_len = size;
  
  __asan_poison_memory_region (poison_buf, poison_len);
}
#else
static void clear_asan_poison (void) { }
static void asan_poison (void const volatile *addr, size_t size) { }
#endif

/* The group separator used when context is requested. */
static const char *group_separator = SEP_STR_GROUP;

/* The context and logic for choosing default --color screen attributes
 (foreground and background colors, etc.) are the following.
 -- There are eight basic colors available, each with its own
 nominal luminosity to the human eye and foreground/background
 codes (black [0 %, 30/40], blue [11 %, 34/44], red [30 %, 31/41],
 magenta [41 %, 35/45], green [59 %, 32/42], cyan [70 %, 36/46],
 yellow [89 %, 33/43], and white [100 %, 37/47]).
 -- Sometimes, white as a background is actually implemented using
 a shade of light gray, so that a foreground white can be visible
 on top of it (but most often not).
 -- Sometimes, black as a foreground is actually implemented using
 a shade of dark gray, so that it can be visible on top of a
 background black (but most often not).
 -- Sometimes, more colors are available, as extensions.
 -- Other attributes can be selected/deselected (bold [1/22],
 underline [4/24], standout/inverse [7/27], blink [5/25], and
 invisible/hidden [8/28]).  They are sometimes implemented by
 using colors instead of what their names imply; e.g., bold is
 often achieved by using brighter colors.  In practice, only bold
 is really available to us, underline sometimes being mapped by
 the terminal to some strange color choice, and standout best
 being left for use by downstream programs such as less(1).
 -- We cannot assume that any of the extensions or special features
 are available for the purpose of choosing defaults for everyone.
 -- The most prevalent default terminal backgrounds are pure black
 and pure white, and are not necessarily the same shades of
 those as if they were selected explicitly with SGR sequences.
 Some terminals use dark or light pictures as default background,
 but those are covered over by an explicit selection of background
 color with an SGR sequence; their users will appreciate their
 background pictures not be covered like this, if possible.
 -- Some uses of colors attributes is to make some output items
 more understated (e.g., context lines); this cannot be achieved
 by changing the background color.
 -- For these reasons, the grep color defaults should strive not
 to change the background color from its default, unless it's
 for a short item that should be highlighted, not understated.
 -- The grep foreground color defaults (without an explicitly set
 background) should provide enough contrast to be readable on any
 terminal with either a black (dark) or white (light) background.
 This only leaves red, magenta, green, and cyan (and their bold
 counterparts) and possibly bold blue.  */
/* The color strings used for matched text.
 The user can overwrite them using the deprecated
 environment variable GREP_COLOR or the new GREP_COLORS.  */
static const char *selected_match_color = "01;31";	/* bold red */
static const char *context_match_color  = "01;31";	/* bold red */

/* Other colors.  Defaults look damn good.  */
static const char *filename_color = "35";	/* magenta */
static const char *line_num_color = "32";	/* green */
static const char *byte_num_color = "32";	/* green */
static const char *sep_color      = "36";	/* cyan */
static const char *selected_line_color = "";	/* default color pair */
static const char *context_line_color  = "";	/* default color pair */

/* Select Graphic Rendition (SGR, "\33[...m") strings.  */
/* Also Erase in Line (EL) to Right ("\33[K") by default.  */
/*    Why have EL to Right after SGR?
 -- The behavior of line-wrapping when at the bottom of the
 terminal screen and at the end of the current line is often
 such that a new line is introduced, entirely cleared with
 the current background color which may be different from the
 default one (see the boolean back_color_erase terminfo(5)
 capability), thus scrolling the display by one line.
 The end of this new line will stay in this background color
 even after reverting to the default background color with
 "\33[m', unless it is explicitly cleared again with "\33[K"
 (which is the behavior the user would instinctively expect
 from the whole thing).  There may be some unavoidable
 background-color flicker at the end of this new line because
 of this (when timing with the monitor's redraw is just right).
 -- The behavior of HT (tab, "\t") is usually the same as that of
 Cursor Forward Tabulation (CHT) with a default parameter
 of 1 ("\33[I"), i.e., it performs pure movement to the next
 tab stop, without any clearing of either content or screen
 attributes (including background color); try
 printf 'asdfqwerzxcv\rASDF\tZXCV\n'
 in a bash(1) shell to demonstrate this.  This is not what the
 user would instinctively expect of HT (but is ok for CHT).
 The instinctive behavior would include clearing the terminal
 cells that are skipped over by HT with blank cells in the
 current screen attributes, including background color;
 the boolean dest_tabs_magic_smso terminfo(5) capability
 indicates this saner behavior for HT, but only some rare
 terminals have it (although it also indicates a special
 glitch with standout mode in the Teleray terminal for which
 it was initially introduced).  The remedy is to add "\33K"
 after each SGR sequence, be it START (to fix the behavior
 of any HT after that before another SGR) or END (to fix the
 behavior of an HT in default background color that would
 follow a line-wrapping at the bottom of the screen in another
 background color, and to complement doing it after START).
 Piping grep's output through a pager such as less(1) avoids
 any HT problems since the pager performs tab expansion.
 
 Generic disadvantages of this remedy are:
 -- Some very rare terminals might support SGR but not EL (nobody
 will use "grep --color" on a terminal that does not support
 SGR in the first place).
 -- Having these extra control sequences might somewhat complicate
 the task of any program trying to parse "grep --color"
 output in order to extract structuring information from it.
 A specific disadvantage to doing it after SGR START is:
 -- Even more possible background color flicker (when timing
 with the monitor's redraw is just right), even when not at the
 bottom of the screen.
 There are no additional disadvantages specific to doing it after
 SGR END.
 
 It would be impractical for GNU grep to become a full-fledged
 terminal program linked against ncurses or the like, so it will
 not detect terminfo(5) capabilities.  */
static const char *sgr_start = "\33[%sm\33[K";
static const char *sgr_end   = "\33[m\33[K";

/* SGR utility functions.  */
static void
pr_sgr_start (char const *s)
{
  if (*s)
    print_start_colorize (sgr_start, s);
}
static void
pr_sgr_end (char const *s)
{
  if (*s)
    print_end_colorize (sgr_end);
}
static void
pr_sgr_start_if (char const *s)
{
  if (color_option)
    pr_sgr_start (s);
}
static void
pr_sgr_end_if (char const *s)
{
  if (color_option)
    pr_sgr_end (s);
}

struct color_cap
{
  const char *name;
  const char **var;
  void (*fct) (void);
};

static void
color_cap_mt_fct (void)
{
  /* Our caller just set selected_match_color.  */
  context_match_color = selected_match_color;
}

static void
color_cap_rv_fct (void)
{
  /* By this point, it was 1 (or already -1).  */
  color_option = -1;  /* That's still != 0.  */
}

static void
color_cap_ne_fct (void)
{
  sgr_start = "\33[%sm";
  sgr_end   = "\33[m";
}

/* For GREP_COLORS.  */
static const struct color_cap color_dict[] =
{
  { "mt", &selected_match_color, color_cap_mt_fct }, /* both ms/mc */
  { "ms", &selected_match_color, NULL }, /* selected matched text */
  { "mc", &context_match_color,  NULL }, /* context matched text */
  { "fn", &filename_color,       NULL }, /* filename */
  { "ln", &line_num_color,       NULL }, /* line number */
  { "bn", &byte_num_color,       NULL }, /* byte (sic) offset */
  { "se", &sep_color,            NULL }, /* separator */
  { "sl", &selected_line_color,  NULL }, /* selected lines */
  { "cx", &context_line_color,   NULL }, /* context lines */
  { "rv", NULL,                  color_cap_rv_fct }, /* -v reverses sl/cx */
  { "ne", NULL,                  color_cap_ne_fct }, /* no EL on SGR_* */
  { NULL, NULL,                  NULL }
};

/* Saved errno value from failed output functions on stdout.  */
static int stdout_errno;

/* buffer for each thread's output */
struct output_buffer_node
{
  char *content;
  char *end;
  intmax_t max_length;
  intmax_t actual_length;
};
static pthread_mutex_t *buffer_lock;

static struct output_buffer_node *output_buffer;
static size_t initial_num_nodes = 32768; /* 2^15 */
static size_t initial_buffstring_length = 128;
static intmax_t current_max_num_nodes;
/* number of nodes before flushing the buffer */
static intmax_t max_allowed_num_nodes;
/* recur == true means to recreate the threads after flushing the buffer */
static bool recur = true;

static void
putchar_errno (int c)
{
  if (putchar (c) < 0)
    stdout_errno = errno;
}
/* Multithreading Version */
static void
putc_errno_mthread (int num_nodes_visited, int c)
{
  pthread_mutex_lock (buffer_lock + (num_nodes_visited % num_threads));
  char **content = &output_buffer[num_nodes_visited].content;
  char **end = &output_buffer[num_nodes_visited].end;
  intmax_t *actual_length_addr = &output_buffer[num_nodes_visited].actual_length;
  intmax_t *max_length_addr = &output_buffer[num_nodes_visited].max_length;
  intmax_t original_max_length = *max_length_addr;
  if (original_max_length - *actual_length_addr < 4)
  {
    if (original_max_length == 0)
    {
      *end =
      *content = (char *) malloc (initial_buffstring_length * sizeof(char));
      *max_length_addr = initial_buffstring_length;
    }
    *max_length_addr += 4;
    *max_length_addr *= 2;
    *content = (char *) realloc (*content, *max_length_addr * sizeof (char));
    *end = *content + *actual_length_addr;
  }
  
  int num_bytes_written;
  if ((num_bytes_written = snprintf (*end, 2, "%c", c)) < 0)
    stdout_errno = errno;
  /* ignoring the null byte by snprintf*/
  *end += (num_bytes_written < 0 ? 0 : num_bytes_written);
  *actual_length_addr += num_bytes_written;
  pthread_mutex_unlock (buffer_lock + (num_nodes_visited % num_threads));
}

static void
fputs_errno (char const *s)
{
  if (fputs (s, stdout) < 0)
    stdout_errno = errno;
}
/* Multithreading version */
static void
fputs_errno_mthread (int num_nodes_visited, char const *s)
{
  pthread_mutex_lock (buffer_lock + (num_nodes_visited % num_threads));
  char **end = &output_buffer[num_nodes_visited].end;
  char **content = &output_buffer[num_nodes_visited].content;
  size_t size = strlen (s) + 1;
  intmax_t *actual_length_addr = &output_buffer[num_nodes_visited].actual_length;
  intmax_t *max_length_addr = &output_buffer[num_nodes_visited].max_length;
  intmax_t original_max_length = *max_length_addr;
  if (original_max_length - *actual_length_addr < size + 4)
  {
    if (original_max_length == 0)
    {
      *end =
      *content = (char *) malloc (initial_buffstring_length * sizeof(char));
      *max_length_addr = initial_buffstring_length;
    }
    *max_length_addr += size + 4;
    *max_length_addr *= 2;
    *content = (char *) realloc (*content, *max_length_addr * sizeof (char));
    *end = *content + *actual_length_addr;
  }
  
  int num_bytes_written;
  if ((num_bytes_written = snprintf (*end, size, "%s", s)) < 0)
    stdout_errno = errno;
  *end += (num_bytes_written < 0 ? 0 : num_bytes_written);
  *actual_length_addr += num_bytes_written;
  pthread_mutex_unlock (buffer_lock + (num_nodes_visited % num_threads));
}

static void _GL_ATTRIBUTE_FORMAT_PRINTF (1, 2)
printf_errno (char const *format, ...)
{
  va_list ap;
  va_start (ap, format);
  if (vfprintf (stdout, format, ap) < 0)
    stdout_errno = errno;
  va_end (ap);
}
/* Multithreading Version */
static void _GL_ATTRIBUTE_FORMAT_PRINTF (3, 4)
printf_errno_mthread (int num_nodes_visited, size_t size, char const *format, ...)
{
  pthread_mutex_lock (buffer_lock + (num_nodes_visited % num_threads));
  char **end = &output_buffer[num_nodes_visited].end;
  char **content = &output_buffer[num_nodes_visited].content;
  intmax_t *actual_length_addr = &output_buffer[num_nodes_visited].actual_length;
  intmax_t *max_length_addr = &output_buffer[num_nodes_visited].max_length;
  intmax_t original_max_length = *max_length_addr;
  if (original_max_length - *actual_length_addr < size + 4)
  {
    if (original_max_length == 0)
    {
      *end = *content = (char *) malloc (initial_buffstring_length * sizeof(char));
      *max_length_addr = initial_buffstring_length;
    }
    *max_length_addr += size + 4;
    *max_length_addr *= 2;
    *content = (char *) realloc (*content, *max_length_addr * sizeof (char));
    *end = *content + *actual_length_addr;
  }
  va_list ap;
  va_start (ap, format);
  int num_bytes_written;
  if ((num_bytes_written = vsnprintf (*end, size, format, ap)) < 0)
    stdout_errno = errno;
  *end += (num_bytes_written < 0 ? 0 : num_bytes_written);
  *actual_length_addr += num_bytes_written;
  va_end (ap);
  pthread_mutex_unlock (buffer_lock + (num_nodes_visited % num_threads));
}

static void
fwrite_errno (void const *ptr, size_t size, size_t nmemb)
{
  if (fwrite (ptr, size, nmemb, stdout) != nmemb)
    stdout_errno = errno;
}
/* Multithreading version */
static void
fwrite_errno_mthread (void const *ptr, size_t size, size_t nmemb, int num_nodes_visited)
{
  pthread_mutex_lock (buffer_lock + (num_nodes_visited % num_threads));
  char **end = &output_buffer[num_nodes_visited].end;
  char **content = &output_buffer[num_nodes_visited].content;
  intmax_t *actual_length_addr = &output_buffer[num_nodes_visited].actual_length;
  intmax_t *max_length_addr = &output_buffer[num_nodes_visited].max_length;
  intmax_t original_max_length = *max_length_addr;
  size_t size_to_copy = size * nmemb;
  if (original_max_length - *actual_length_addr < size_to_copy + 4)
  {
    if (original_max_length == 0)
    {
      *end = *content = (char *) malloc (initial_buffstring_length * sizeof(char));
      *max_length_addr = initial_buffstring_length;
    }
    *max_length_addr += size_to_copy * 2;
    *max_length_addr *= 2;
    *content =
    (char *) realloc(*content, *max_length_addr * sizeof (char));
    *end = *content + *actual_length_addr;
  }
  *end = mempcpy (*end, ptr, size_to_copy);
  *actual_length_addr += size_to_copy;
  if (*end == NULL)
    stdout_errno = errno;
  pthread_mutex_unlock (buffer_lock + (num_nodes_visited % num_threads));
}

static void
fflush_errno (void)
{
  if (fflush (stdout) != 0)
    stdout_errno = errno;
}
/* Multithreading version */
/* we never use line buffering with -r */
/* static void
 fflush_errno_mthread (FILE *fd)
 {
 if (fflush (fd) != 0)
 stdout_errno = errno;
 }
 */

/* Multithreading version */
static void
pr_sgr_start_mthread (char const *s, int num_nodes_visited)
{
  if (*s)
  {
    printf_errno_mthread (num_nodes_visited,
                          strlen (sgr_start) + strlen (s) + 5, sgr_start, s);
  }
}
/* Multithreading version */
static void
pr_sgr_end_mthread (char const *s, int num_nodes_visited)
{
  if (*s)
    fputs_errno_mthread (num_nodes_visited, sgr_end);
}

static void
pr_sgr_start_if_mthread (char const *s, int num_nodes_visited)
{
  if (color_option)
    pr_sgr_start_mthread (s, num_nodes_visited);
}
static void
pr_sgr_end_if_mthread (char const *s, int num_nodes_visited)
{
  if (color_option)
    pr_sgr_end_mthread (s, num_nodes_visited);
}

static struct exclude *excluded_patterns[2];
static struct exclude *excluded_directory_patterns[2];
/* Short options.  */
static char const short_options[] =
"0123456789A:B:C:D:EFGHIPTUVX:abcd:e:f:hiLlm:nop:qRrsuvwxyZz";

/* Non-boolean long options that have no corresponding short equivalents.  */
enum
{
  BINARY_FILES_OPTION = CHAR_MAX + 1,
  COLOR_OPTION,
  EXCLUDE_DIRECTORY_OPTION,
  EXCLUDE_OPTION,
  EXCLUDE_FROM_OPTION,
  GROUP_SEPARATOR_OPTION,
  INCLUDE_OPTION,
  LINE_BUFFERED_OPTION,
  LABEL_OPTION
};

/* Long options equivalences. */
static struct option const long_options[] =
{
  {"basic-regexp",    no_argument, NULL, 'G'},
  {"extended-regexp", no_argument, NULL, 'E'},
  {"fixed-regexp",    no_argument, NULL, 'F'},
  {"fixed-strings",   no_argument, NULL, 'F'},
  {"perl-regexp",     no_argument, NULL, 'P'},
  {"after-context", required_argument, NULL, 'A'},
  {"before-context", required_argument, NULL, 'B'},
  {"binary-files", required_argument, NULL, BINARY_FILES_OPTION},
  {"byte-offset", no_argument, NULL, 'b'},
  {"context", required_argument, NULL, 'C'},
  {"color", optional_argument, NULL, COLOR_OPTION},
  {"colour", optional_argument, NULL, COLOR_OPTION},
  {"count", no_argument, NULL, 'c'},
  {"devices", required_argument, NULL, 'D'},
  {"directories", required_argument, NULL, 'd'},
  {"exclude", required_argument, NULL, EXCLUDE_OPTION},
  {"exclude-from", required_argument, NULL, EXCLUDE_FROM_OPTION},
  {"exclude-dir", required_argument, NULL, EXCLUDE_DIRECTORY_OPTION},
  {"file", required_argument, NULL, 'f'},
  {"files-with-matches", no_argument, NULL, 'l'},
  {"files-without-match", no_argument, NULL, 'L'},
  {"group-separator", required_argument, NULL, GROUP_SEPARATOR_OPTION},
  {"help", no_argument, &show_help, 1},
  {"include", required_argument, NULL, INCLUDE_OPTION},
  {"ignore-case", no_argument, NULL, 'i'},
  {"initial-tab", no_argument, NULL, 'T'},
  {"label", required_argument, NULL, LABEL_OPTION},
  {"line-buffered", no_argument, NULL, LINE_BUFFERED_OPTION},
  {"line-number", no_argument, NULL, 'n'},
  {"line-regexp", no_argument, NULL, 'x'},
  {"max-count", required_argument, NULL, 'm'},
  
  {"no-filename", no_argument, NULL, 'h'},
  {"no-group-separator", no_argument, NULL, GROUP_SEPARATOR_OPTION},
  {"no-messages", no_argument, NULL, 's'},
  {"null", no_argument, NULL, 'Z'},
  {"null-data", no_argument, NULL, 'z'},
  {"only-matching", no_argument, NULL, 'o'},
  {"quiet", no_argument, NULL, 'q'},
  {"recursive", no_argument, NULL, 'r'},
  {"dereference-recursive", no_argument, NULL, 'R'},
  {"regexp", required_argument, NULL, 'e'},
  {"invert-match", no_argument, NULL, 'v'},
  {"silent", no_argument, NULL, 'q'},
  {"text", no_argument, NULL, 'a'},
  {"binary", no_argument, NULL, 'U'},
  {"unix-byte-offsets", no_argument, NULL, 'u'},
  {"version", no_argument, NULL, 'V'},
  {"with-filename", no_argument, NULL, 'H'},
  {"word-regexp", no_argument, NULL, 'w'},
  {0, 0, 0, 0}
};

/* Define flags declared in grep.h. */
bool match_icase;
bool match_words;
bool match_lines;
char eolbyte;

static char const *matcher;

/* For error messages. */
/* The input file name, or (if standard input) "-" or a --label argument.  */
static char const *filename;
/* Omit leading "./" from file names in diagnostics.  */
static bool omit_dot_slash;
static bool errseen;

/* True if output from the current input file has been suppressed
 because an output line had an encoding error.  */
static bool encoding_error_output;

enum directories_type
{
  READ_DIRECTORIES = 2,
  RECURSE_DIRECTORIES,
  SKIP_DIRECTORIES
};

/* How to handle directories.  */
static char const *const directories_args[] =
{
  "read", "recurse", "skip", NULL
};
static enum directories_type const directories_types[] =
{
  READ_DIRECTORIES, RECURSE_DIRECTORIES, SKIP_DIRECTORIES
};
ARGMATCH_VERIFY (directories_args, directories_types);

static enum directories_type directories = READ_DIRECTORIES;

enum { basic_fts_options = FTS_CWDFD | FTS_NOSTAT | FTS_TIGHT_CYCLE_CHECK };
static int fts_options = basic_fts_options | FTS_COMFOLLOW | FTS_PHYSICAL;

/* How to handle devices. */
static enum
{
  READ_COMMAND_LINE_DEVICES,
  READ_DEVICES,
  SKIP_DEVICES
} devices = READ_COMMAND_LINE_DEVICES;

/* local struct information variable used in multithreading */
struct grep_info
{
  bool done_on_match;
  bool out_quiet;
  bool skip_nuls;     /* to be initialized inside the grep function call */
  bool encoding_error_output;
  bool seek_data_failed;
  bool skip_empty_lines;
  int out_file;
  int thread_id;
  int bufdesc;
  char const *filename;
  char const *lastnl; /* to be initialized inside the grep function call */
  char *bufbeg;       /* to be initialized inside the grep function call */
  char *buflim;       /* to be initialized inside the grep function call */
  char *lastout;
  char *buffer;
  size_t bufalloc;
  size_t pagesize;
  intmax_t outleft;
  intmax_t pending;
  uintmax_t totalnl;
  uintmax_t totalcc;
  off_t bufoffset;
  off_t after_last_match;
};

struct thread_routine_arg
{
  bool command_line_local;
  bool no_filenames;
  int thread_id;
  int num_nodes_visited;
  char const *filename_local;
  intmax_t current_max_num_nodes;
};

static bool *status_array;  /* return status for each thread */
static pthread_t *threads;
static struct thread_routine_arg *thread_routine_arg_array;
static struct grep_info *grep_info_array;

static bool grepfile (int, char const *, bool, bool);
static bool grepfile_mthread (int, char const *, bool, bool, int);
static intmax_t grep_mthread (int, struct stat const *, struct grep_info *);

void initialize_grep_info (struct grep_info *);
static bool grepdesc (int, bool);
static bool grepdesc_traversal_mthread (int, bool);
static bool grepdesc_mthread (int, bool, int);
void * thread_routine(void *arg);


static void dos_binary (void);
static void dos_unix_byte_offsets (void);
static size_t undossify_input (char *, size_t);
static size_t undossify_input_mthread (char *, size_t, char *);

void raise_max_nodes (int num_nodes_visited);
void
raise_max_nodes (int num_nodes_visited)
{
  if (num_nodes_visited < current_max_num_nodes - 2)
    return;
  current_max_num_nodes *= 2;
  output_buffer = (struct output_buffer_node *) realloc (output_buffer, current_max_num_nodes * sizeof (struct output_buffer_node));
  if (output_buffer == NULL)
    xalloc_die();
  for (size_t i = current_max_num_nodes / 2; i < current_max_num_nodes; ++i)
  {
    output_buffer[i].max_length = 0;
    output_buffer[i].actual_length = 0;
  }
  for (int i = 0; i < num_threads; ++i)
  {
    thread_routine_arg_array[i].current_max_num_nodes = current_max_num_nodes;
  }
}

void lock_buffer_locks (void);
void
lock_buffer_locks (void)
{
  for (int i = 0; i < num_threads; ++i)
  {
    pthread_mutex_lock (buffer_lock + i);
  }
}

void unlock_buffer_locks (void);
void unlock_buffer_locks (void)
{
  for (int i = 0; i < num_threads; ++i)
  {
    pthread_mutex_unlock (buffer_lock + i);
  }
}

static bool
is_device_mode (mode_t m)
{
  return S_ISCHR (m) || S_ISBLK (m) || S_ISSOCK (m) || S_ISFIFO (m);
}

static bool
skip_devices (bool command_line)
{
  return (devices == SKIP_DEVICES
          || ((devices == READ_COMMAND_LINE_DEVICES) & !command_line));
}

/* Return if ST->st_size is defined.  Assume the file is not a
 symbolic link.  */
static bool
usable_st_size (struct stat const *st)
{
  return S_ISREG (st->st_mode) || S_TYPEISSHM (st) || S_TYPEISTMO (st);
}

/* Lame substitutes for SEEK_DATA and SEEK_HOLE on platforms lacking them.
 Do not rely on these finding data or holes if they equal SEEK_SET.  */
#ifndef SEEK_DATA
enum { SEEK_DATA = SEEK_SET };
#endif
#ifndef SEEK_HOLE
enum { SEEK_HOLE = SEEK_SET };
#endif

/* Functions we'll use to search. */
typedef void (*compile_fp_t) (char const *, size_t);
typedef size_t (*execute_fp_t) (char *, size_t, size_t *, char const *);
static compile_fp_t compile;
static execute_fp_t execute;

/* Like error, but suppress the diagnostic if requested.  */
static void
suppressible_error (char const *mesg, int errnum)
{
  if (! suppress_errors)
    error (0, errnum, "%s", mesg);
  errseen = true;
}

/* If there has already been a write error, don't bother closing
 standard output, as that might elicit a duplicate diagnostic.  */
static void
clean_up_stdout (void)
{
  if (! stdout_errno)
    close_stdout ();
}

/* A cast to TYPE of VAL.  Use this when TYPE is a pointer type, VAL
 is properly aligned for TYPE, and 'gcc -Wcast-align' cannot infer
 the alignment and would otherwise complain about the cast.  */
#if 4 < __GNUC__ + (6 <= __GNUC_MINOR__)
# define CAST_ALIGNED(type, val)                           \
({ __typeof__ (val) val_ = val;                        \
_Pragma ("GCC diagnostic push")                     \
_Pragma ("GCC diagnostic ignored \"-Wcast-align\"") \
(type) val_;                                        \
_Pragma ("GCC diagnostic pop")                      \
})
#else
# define CAST_ALIGNED(type, val) ((type) (val))
#endif

/* An unsigned type suitable for fast matching.  */
typedef uintmax_t uword;

/* A mask to test for unibyte characters, with the pattern repeated to
 fill a uword.  For a multibyte character encoding where
 all bytes are unibyte characters, this is 0.  For UTF-8, this is
 0x808080....  For encodings where unibyte characters have no discerned
 pattern, this is all 1s.  The unsigned char C is a unibyte
 character if C & UNIBYTE_MASK is zero.  If the uword W is the
 concatenation of bytes, the bytes are all unibyte characters
 if W & UNIBYTE_MASK is zero.  */
static uword unibyte_mask;

static void
initialize_unibyte_mask (void)
{
  /* For each encoding error I that MASK does not already match,
   accumulate I's most significant 1 bit by ORing it into MASK.
   Although any 1 bit of I could be used, in practice high-order
   bits work better.  */
  unsigned char mask = 0;
  int ms1b = 1;
  for (int i = 1; i <= UCHAR_MAX; i++)
    if ((localeinfo.sbclen[i] != 1) & ! (mask & i))
    {
      while (ms1b * 2 <= i)
        ms1b *= 2;
      mask |= ms1b;
    }
  
  /* Now MASK will detect any encoding-error byte, although it may
   cry wolf and it may not be optimal.  Build a uword-length mask by
   repeating MASK.  */
  uword uword_max = -1;
  unibyte_mask = uword_max / UCHAR_MAX * mask;
}

/* Skip the easy bytes in a buffer that is guaranteed to have a sentinel
 that is not easy, and return a pointer to the first non-easy byte.
 The easy bytes all have UNIBYTE_MASK off.  */
static char const * _GL_ATTRIBUTE_PURE
skip_easy_bytes (char const *buf)
{
  /* Search a byte at a time until the pointer is aligned, then a
   uword at a time until a match is found, then a byte at a time to
   identify the exact byte.  The uword search may go slightly past
   the buffer end, but that's benign.  */
  char const *p;
  uword const *s;
  for (p = buf; (uintptr_t) p % sizeof (uword) != 0; p++)
    if (to_uchar (*p) & unibyte_mask)
      return p;
  for (s = CAST_ALIGNED (uword const *, p); ! (*s & unibyte_mask); s++)
    continue;
  for (p = (char const *) s; ! (to_uchar (*p) & unibyte_mask); p++)
    continue;
  return p;
}

/* Return true if BUF, of size SIZE, has an encoding error.
 BUF must be followed by at least sizeof (uword) bytes,
 the first of which may be modified.  */
bool
buf_has_encoding_errors (char *buf, size_t size)
{
  if (! unibyte_mask)
    return false;
  
  mbstate_t mbs = { 0 };
  size_t clen;
  
  buf[size] = -1;
  for (char const *p = buf; (p = skip_easy_bytes (p)) < buf + size; p += clen)
  {
    clen = mbrlen (p, buf + size - p, &mbs);
    if ((size_t) -2 <= clen)
      return true;
  }
  
  return false;
}


/* Return true if BUF, of size SIZE, has a null byte.
 BUF must be followed by at least one byte,
 which may be arbitrarily written to or read from.  */
static bool
buf_has_nulls (char *buf, size_t size)
{
  buf[size] = 0;
  return strlen (buf) != size;
}

/* Return true if a file is known to contain null bytes.
 SIZE bytes have already been read from the file
 with descriptor FD and status ST.  */
static bool
file_must_have_nulls (size_t size, int fd, struct stat const *st)
{
  if (usable_st_size (st))
  {
    if (st->st_size <= size)
      return false;
    
    /* If the file has holes, it must contain a null byte somewhere.  */
    if (SEEK_HOLE != SEEK_SET)
    {
      off_t cur = size;
      if (O_BINARY || fd == STDIN_FILENO)
      {
        cur = lseek (fd, 0, SEEK_CUR);
        if (cur < 0)
          return false;
      }
      
      /* Look for a hole after the current location.  */
      off_t hole_start = lseek (fd, cur, SEEK_HOLE);
      if (0 <= hole_start)
      {
        if (lseek (fd, cur, SEEK_SET) < 0)
          suppressible_error (filename, errno);
        if (hole_start < st->st_size)
          return true;
      }
    }
  }
  
  return false;
}

/* Multithreading version */
static bool
file_must_have_nulls_mthread (size_t size, int fd, struct stat const *st, struct grep_info *info)
{
  if (usable_st_size (st))
  {
    if (st->st_size <= size)
      return false;
    
    /* If the file has holes, it must contain a null byte somewhere.  */
    if (SEEK_HOLE != SEEK_SET)
    {
      off_t cur = size;
      if (O_BINARY || fd == STDIN_FILENO)
      {
        cur = lseek (fd, 0, SEEK_CUR);
        if (cur < 0)
          return false;
      }
      
      /* Look for a hole after the current location.  */
      off_t hole_start = lseek (fd, cur, SEEK_HOLE);
      if (0 <= hole_start)
      {
        if (lseek (fd, cur, SEEK_SET) < 0)
          suppressible_error (info->filename, errno);
        if (hole_start < st->st_size)
          return true;
      }
    }
  }
  
  return false;
}

/* Convert STR to a nonnegative integer, storing the result in *OUT.
 STR must be a valid context length argument; report an error if it
 isn't.  Silently ceiling *OUT at the maximum value, as that is
 practically equivalent to infinity for grep's purposes.  */
static void
context_length_arg (char const *str, intmax_t *out)
{
  switch (xstrtoimax (str, 0, 10, out, ""))
  {
    case LONGINT_OK:
    case LONGINT_OVERFLOW:
      if (0 <= *out)
        break;
      /* Fall through.  */
    default:
      error (EXIT_TROUBLE, 0, "%s: %s", str,
             _("invalid context length argument"));
  }
}

/* Return the add_exclude options suitable for excluding a file name.
 If COMMAND_LINE, it is a command-line file name.  */
static int
exclude_options (bool command_line)
{
  return EXCLUDE_WILDCARDS | (command_line ? 0 : EXCLUDE_ANCHORED);
}

/* Return true if the file with NAME should be skipped.
 If COMMAND_LINE, it is a command-line argument.
 If IS_DIR, it is a directory.  */
static bool
skipped_file (char const *name, bool command_line, bool is_dir)
{
  struct exclude **pats;
  if (! is_dir)
    pats = excluded_patterns;
  else if (directories == SKIP_DIRECTORIES)
    return true;
  else if (command_line && omit_dot_slash)
    return false;
  else
    pats = excluded_directory_patterns;
  return pats[command_line] && excluded_file_name (pats[command_line], name);
}

/* Hairy buffering mechanism for grep.  The intent is to keep
 all reads aligned on a page boundary and multiples of the
 page size, unless a read yields a partial page.  */

static char *buffer;		/* Base of buffer. */
static size_t bufalloc;		/* Allocated buffer size, counting slop. */
#define INITIAL_BUFSIZE 32768	/* Initial buffer size, not counting slop. */
static int bufdesc;		/* File descriptor. */
static char *bufbeg;		/* Beginning of user-visible stuff. */
static char *buflim;		/* Limit of user-visible stuff. */
static size_t pagesize;		/* alignment of memory pages */
static off_t bufoffset;		/* Read offset; defined on regular files.  */
static off_t after_last_match;	/* Pointer after last matching line that
                                 would have been output if we were
                                 outputting characters. */
static bool skip_nuls;		/* Skip '\0' in data.  */
static bool skip_empty_lines;	/* Skip empty lines in data.  */
static bool seek_data_failed;	/* lseek with SEEK_DATA failed.  */
static uintmax_t totalnl;	/* Total newline count before lastnl. */

/* Return VAL aligned to the next multiple of ALIGNMENT.  VAL can be
 an integer or a pointer.  Both args must be free of side effects.  */
#define ALIGN_TO(val, alignment) \
((size_t) (val) % (alignment) == 0 \
? (val) \
: (val) + ((alignment) - (size_t) (val) % (alignment)))

/* Add two numbers that count input bytes or lines, and report an
 error if the addition overflows.  */
static uintmax_t
add_count (uintmax_t a, uintmax_t b)
{
  uintmax_t sum = a + b;
  if (sum < a)
    error (EXIT_TROUBLE, 0, _("input is too large to count"));
  return sum;
}

/* Return true if BUF (of size SIZE) is all zeros.  */
static bool
all_zeros (char const *buf, size_t size)
{
  for (char const *p = buf; p < buf + size; p++)
    if (*p)
      return false;
  return true;
}

/* Reset the buffer for a new file, returning false if we should skip it.
 Initialize on the first time through. */
static bool
reset (int fd, struct stat const *st)
{
  bufbeg = buflim = ALIGN_TO (buffer + 1, pagesize);
  bufbeg[-1] = eolbyte;
  bufdesc = fd;
  
  if (S_ISREG (st->st_mode))
  {
    if (fd != STDIN_FILENO)
      bufoffset = 0;
    else
    {
      bufoffset = lseek (fd, 0, SEEK_CUR);
      if (bufoffset < 0)
      {
        suppressible_error (_("lseek failed"), errno);
        return false;
      }
    }
  }
  return true;
}

/* Multithreading version */
static bool
reset_mthread (int fd, struct stat const *st, struct grep_info *info)
{
  info->bufbeg = info->buflim = ALIGN_TO (info->buffer + 1, pagesize);
  (info->bufbeg)[-1] = eolbyte;
  info->bufdesc = fd;
  
  if (S_ISREG (st->st_mode))
  {
    if (fd != STDIN_FILENO)
      info->bufoffset = 0;
    else
    {
      info->bufoffset = lseek (fd, 0, SEEK_CUR);
      if (info->bufoffset < 0)
      {
        suppressible_error (_("lseek failed"), errno);
        return false;
      }
    }
  }
  return true;
}

/* Read new stuff into the buffer, saving the specified
 amount of old stuff.  When we're done, 'bufbeg' points
 to the beginning of the buffer contents, and 'buflim'
 points just after the end.  Return false if there's an error.  */
static bool
fillbuf (size_t save, struct stat const *st)
{
  size_t fillsize;
  bool cc = true;
  char *readbuf;
  size_t readsize;
  
  /* Offset from start of buffer to start of old stuff
   that we want to save.  */
  size_t saved_offset = buflim - save - buffer;
  
  if (pagesize <= buffer + bufalloc - sizeof (uword) - buflim)
  {
    readbuf = buflim;
    bufbeg = buflim - save;
  }
  else
  {
    size_t minsize = save + pagesize;
    size_t newsize;
    size_t newalloc;
    char *newbuf;
    
    /* Grow newsize until it is at least as great as minsize.  */
    for (newsize = bufalloc - pagesize - sizeof (uword);
         newsize < minsize;
         newsize *= 2)
      if ((SIZE_MAX - pagesize - sizeof (uword)) / 2 < newsize)
        xalloc_die ();
    
    /* Try not to allocate more memory than the file size indicates,
     as that might cause unnecessary memory exhaustion if the file
     is large.  However, do not use the original file size as a
     heuristic if we've already read past the file end, as most
     likely the file is growing.  */
    if (usable_st_size (st))
    {
      off_t to_be_read = st->st_size - bufoffset;
      off_t maxsize_off = save + to_be_read;
      if (0 <= to_be_read && to_be_read <= maxsize_off
          && maxsize_off == (size_t) maxsize_off
          && minsize <= (size_t) maxsize_off
          && (size_t) maxsize_off < newsize)
        newsize = maxsize_off;
    }
    
    /* Add enough room so that the buffer is aligned and has room
     for byte sentinels fore and aft, and so that a uword can
     be read aft.  */
    newalloc = newsize + pagesize + sizeof (uword);
    
    newbuf = bufalloc < newalloc ? xmalloc (bufalloc = newalloc) : buffer;
    readbuf = ALIGN_TO (newbuf + 1 + save, pagesize);
    bufbeg = readbuf - save;
    memmove (bufbeg, buffer + saved_offset, save);
    bufbeg[-1] = eolbyte;
    if (newbuf != buffer)
    {
      free (buffer);
      buffer = newbuf;
    }
  }
  
  clear_asan_poison ();
  
  readsize = buffer + bufalloc - sizeof (uword) - readbuf;
  readsize -= readsize % pagesize;
  
  while (true)
  {
    fillsize = safe_read (bufdesc, readbuf, readsize);
    if (fillsize == SAFE_READ_ERROR)
    {
      fillsize = 0;
      cc = false;
    }
    bufoffset += fillsize;
    
    if (((fillsize == 0) | !skip_nuls) || !all_zeros (readbuf, fillsize))
      break;
    totalnl = add_count (totalnl, fillsize);
    
    if (SEEK_DATA != SEEK_SET && !seek_data_failed)
    {
      /* Solaris SEEK_DATA fails with errno == ENXIO in a hole at EOF.  */
      off_t data_start = lseek (bufdesc, bufoffset, SEEK_DATA);
      if (data_start < 0 && errno == ENXIO
          && usable_st_size (st) && bufoffset < st->st_size)
        data_start = lseek (bufdesc, 0, SEEK_END);
      
      if (data_start < 0)
        seek_data_failed = true;
      else
      {
        totalnl = add_count (totalnl, data_start - bufoffset);
        bufoffset = data_start;
      }
    }
  }
  
  fillsize = undossify_input (readbuf, fillsize);
  buflim = readbuf + fillsize;
  
  /* Initialize the following word, because skip_easy_bytes and some
   matchers read (but do not use) those bytes.  This avoids false
   positive reports of these bytes being used uninitialized.  */
  memset (buflim, 0, sizeof (uword));
  
  /* Mark the part of the buffer not filled by the read or set by
   the above memset call as ASAN-poisoned.  */
  asan_poison (buflim + sizeof (uword),
               bufalloc - (buflim - buffer) - sizeof (uword));
  
  return cc;
}

/* Multithreading version */
static bool
fillbuf_mthread (size_t save, struct stat const *st, struct grep_info *info)
{
  size_t fillsize;
  bool cc = true;
  char *readbuf;
  size_t readsize;
  
  /* Offset from start of buffer to start of old stuff
   that we want to save.  */
  size_t saved_offset = info->buflim - save - info->buffer;
  
  if (info->pagesize <= info->buffer + info->bufalloc - sizeof (uword) - info->buflim)
  {
    readbuf = info->buflim;
    info->bufbeg = info->buflim - save;
  }
  else
  {
    size_t minsize = save + info->pagesize;
    size_t newsize;
    size_t newalloc;
    char *newbuf;
    
    /* Grow newsize until it is at least as great as minsize.  */
    for (newsize = info->bufalloc - info->pagesize - sizeof (uword);
         newsize < minsize;
         newsize *= 2)
      if ((SIZE_MAX - info->pagesize - sizeof (uword)) / 2 < newsize)
        xalloc_die ();
    
    /* Try not to allocate more memory than the file size indicates,
     as that might cause unnecessary memory exhaustion if the file
     is large.  However, do not use the original file size as a
     heuristic if we've already read past the file end, as most
     likely the file is growing.  */
    if (usable_st_size (st))
    {
      off_t to_be_read = st->st_size - info->bufoffset;
      off_t maxsize_off = save + to_be_read;
      if (0 <= to_be_read && to_be_read <= maxsize_off
          && maxsize_off == (size_t) maxsize_off
          && minsize <= (size_t) maxsize_off
          && (size_t) maxsize_off < newsize)
        newsize = maxsize_off;
    }
    
    /* Add enough room so that the buffer is aligned and has room
     for byte sentinels fore and aft, and so that a uword can
     be read aft.  */
    newalloc = newsize + info->pagesize + sizeof (uword);
    
    newbuf = info->bufalloc < newalloc ? xmalloc (info->bufalloc = newalloc) : info->buffer;
    readbuf = ALIGN_TO (newbuf + 1 + save, info->pagesize);
    info->bufbeg = readbuf - save;
    memmove (info->bufbeg, info->buffer + saved_offset, save);
    (info->bufbeg)[-1] = eolbyte;
    if (newbuf != info->buffer)
    {
      free (info->buffer);
      info->buffer = newbuf;
    }
  }
  
  clear_asan_poison ();
  
  readsize = info->buffer + info->bufalloc - sizeof (uword) - readbuf;
  readsize -= readsize % info->pagesize;
  
  while (true)
  {
    fillsize = safe_read (info->bufdesc, readbuf, readsize);
    if (fillsize == SAFE_READ_ERROR)
    {
      fillsize = 0;
      cc = false;
    }
    info->bufoffset += fillsize;
    
    if (((fillsize == 0) | !info->skip_nuls) || !all_zeros (readbuf, fillsize))
      break;
    info->totalnl = add_count (info->totalnl, fillsize);
    
    if (SEEK_DATA != SEEK_SET && !info->seek_data_failed)
    {
      /* Solaris SEEK_DATA fails with errno == ENXIO in a hole at EOF.  */
      off_t data_start = lseek (info->bufdesc, info->bufoffset, SEEK_DATA);
      if (data_start < 0 && errno == ENXIO
          && usable_st_size (st) && info->bufoffset < st->st_size)
        data_start = lseek (info->bufdesc, 0, SEEK_END);
      
      if (data_start < 0)
        info->seek_data_failed = true;
      else
      {
        info->totalnl = add_count (info->totalnl, data_start - info->bufoffset);
        info->bufoffset = data_start;
      }
    }
  }
  
  fillsize = undossify_input_mthread (readbuf, fillsize, info->bufbeg);
  info->buflim = readbuf + fillsize;
  
  /* Initialize the following word, because skip_easy_bytes and some
   matchers read (but do not use) those bytes.  This avoids false
   positive reports of these bytes being used uninitialized.  */
  memset (info->buflim, 0, sizeof (uword));
  
  /* Mark the part of the buffer not filled by the read or set by
   the above memset call as ASAN-poisoned.  */
  asan_poison (info->buflim + sizeof (uword),
               info->bufalloc - (info->buflim - info->buffer) - sizeof (uword));
  
  return cc;
}

/* Flags controlling the style of output. */
static enum
{
  BINARY_BINARY_FILES,
  TEXT_BINARY_FILES,
  WITHOUT_MATCH_BINARY_FILES
} binary_files;		/* How to handle binary files.  */

/* Options for output as a list of matching/non-matching files */
static enum
{
  LISTFILES_NONE,
  LISTFILES_MATCHING,
  LISTFILES_NONMATCHING,
} list_files;

static int filename_mask;	/* If zero, output nulls after filenames.  */
static bool out_quiet;		/* Suppress all normal output. */
static bool out_invert;		/* Print nonmatching stuff. */
static int out_file;		/* Print filenames. */
static bool out_line;		/* Print line numbers. */
static bool out_byte;		/* Print byte offsets. */
static intmax_t out_before;	/* Lines of leading context. */
static intmax_t out_after;	/* Lines of trailing context. */
static bool count_matches;	/* Count matching lines.  */
static bool no_filenames;	/* Suppress file names.  */
static intmax_t max_count;	/* Stop after outputting this many
                             lines from an input file.  */
static bool line_buffered;	/* Use line buffering.  */
static char *label = NULL;      /* Fake filename for stdin */

FTS **fts_global_array;            /* FTS variable for multithreading */

/* Internal variables to keep track of byte count, context, etc. */
static uintmax_t totalcc;	/* Total character count before bufbeg. */
static char const *lastnl;	/* Pointer after last newline counted. */
static char *lastout;		/* Pointer after last character output;
                         NULL if no character has been output
                         or if it's conceptually before bufbeg. */
static intmax_t outleft;	/* Maximum number of lines to be output.  */
static intmax_t pending;	/* Pending lines of output.
                           Always kept 0 if out_quiet is true.  */
static bool done_on_match;	/* Stop scanning file on first match.  */
static bool exit_on_match;	/* Exit on first match.  */

#include "dosbuf.c"

static void
nlscan (char const *lim)
{
  size_t newlines = 0;
  char const *beg;
  for (beg = lastnl; beg < lim; beg++)
  {
    beg = memchr (beg, eolbyte, lim - beg);
    if (!beg)
      break;
    newlines++;
  }
  totalnl = add_count (totalnl, newlines);
  lastnl = lim;
}

/* Multithreading version */
static void
nlscan_mthread (char const *lim, struct grep_info *info)
{
  size_t newlines = 0;
  char const *beg;
  for (beg = info->lastnl; beg < lim; beg++)
  {
    beg = memchr (beg, eolbyte, lim - beg);
    if (!beg)
      break;
    newlines++;
  }
  info->totalnl = add_count (info->totalnl, newlines);
  info->lastnl = lim;
}

/* Print the current filename.  */
static void
print_filename (void)
{
  pr_sgr_start_if (filename_color);
  fputs_errno (filename);
  pr_sgr_end_if (filename_color);
}

/* Print the current filename. Used for multithreading.  */
static void
print_filename_in_thread (char const *fname, int num_nodes_visited)
{
  pr_sgr_start_if_mthread (filename_color, num_nodes_visited);
  fputs_errno_mthread(num_nodes_visited, fname);
  pr_sgr_end_if_mthread (filename_color, num_nodes_visited);
}


/* Print a character separator.  */
static void
print_sep (char sep)
{
  pr_sgr_start_if (sep_color);
  putchar_errno (sep);
  pr_sgr_end_if (sep_color);
}
/* Multithreading version */
static void
print_sep_mthread (char sep, int num_nodes_visited)
{
  pr_sgr_start_if_mthread (sep_color, num_nodes_visited);
  putc_errno_mthread (num_nodes_visited, sep);
  pr_sgr_end_if_mthread (sep_color, num_nodes_visited);
}

/* Print a line number or a byte offset.  */
static void
print_offset (uintmax_t pos, int min_width, const char *color)
{
  /* Do not rely on printf to print pos, since uintmax_t may be longer
   than long, and long long is not portable.  */
  
  char buf[sizeof pos * CHAR_BIT];
  char *p = buf + sizeof buf;
  
  do
  {
    *--p = '0' + pos % 10;
    --min_width;
  }
  while ((pos /= 10) != 0);
  
  /* Do this to maximize the probability of alignment across lines.  */
  if (align_tabs)
    while (--min_width >= 0)
      *--p = ' ';
  
  pr_sgr_start_if (color);
  fwrite_errno (p, 1, buf + sizeof buf - p);
  pr_sgr_end_if (color);
}
/* Multithrading version */
static void
print_offset_mthread (uintmax_t pos, int min_width, const char *color, int num_nodes_visited)
{
  /* Do not rely on printf to print pos, since uintmax_t may be longer
   than long, and long long is not portable.  */
  
  char buf[sizeof pos * CHAR_BIT];
  char *p = buf + sizeof buf;
  
  do
  {
    *--p = '0' + pos % 10;
    --min_width;
  }
  while ((pos /= 10) != 0);
  
  /* Do this to maximize the probability of alignment across lines.  */
  if (align_tabs)
    while (--min_width >= 0)
      *--p = ' ';
  
  pr_sgr_start_if_mthread (color, num_nodes_visited);
  fwrite_errno_mthread (p, 1, buf + sizeof buf - p, num_nodes_visited);
  pr_sgr_end_if_mthread (color, num_nodes_visited);
}

/* Print a whole line head (filename, line, byte).  The output data
 starts at BEG and contains LEN bytes; it is followed by at least
 sizeof (uword) bytes, the first of which may be temporarily modified.
 The output data comes from what is perhaps a larger input line that
 goes until LIM, where LIM[-1] is an end-of-line byte.  Use SEP as
 the separator on output.
 
 Return true unless the line was suppressed due to an encoding error.  */

static bool
print_line_head (char *beg, size_t len, char const *lim, char sep)
{
  if (binary_files != TEXT_BINARY_FILES)
  {
    char ch = beg[len];
    bool encoding_errors = buf_has_encoding_errors (beg, len);
    beg[len] = ch;
    if (encoding_errors)
    {
      encoding_error_output = true;
      return false;
    }
  }
  
  bool pending_sep = false;
  
  if (out_file)
  {
    print_filename ();
    if (filename_mask)
      pending_sep = true;
    else
      putchar_errno (0);
  }
  
  if (out_line)
  {
    if (lastnl < lim)
    {
      nlscan (beg);
      totalnl = add_count (totalnl, 1);
      lastnl = lim;
    }
    if (pending_sep)
      print_sep (sep);
    print_offset (totalnl, 4, line_num_color);
    pending_sep = true;
  }
  
  if (out_byte)
  {
    uintmax_t pos = add_count (totalcc, beg - bufbeg);
    pos = dossified_pos (pos);
    if (pending_sep)
      print_sep (sep);
    print_offset (pos, 6, byte_num_color);
    pending_sep = true;
  }
  
  if (pending_sep)
  {
    /* This assumes sep is one column wide.
     Try doing this any other way with Unicode
     (and its combining and wide characters)
     filenames and you're wasting your efforts.  */
    if (align_tabs)
      fputs_errno ("\t\b");
    
    print_sep (sep);
  }
  
  return true;
}


/* Multithreading version */
static bool
print_line_head_mthread (char *beg, size_t len, char const *lim, char sep, struct grep_info *info)
{
  int num_nodes_visited = thread_routine_arg_array[info->thread_id].num_nodes_visited;
  bool encoding_errors = false;
  if (binary_files != TEXT_BINARY_FILES)
  {
    char ch = beg[len];
    encoding_errors = buf_has_encoding_errors (beg, len);
    beg[len] = ch;
  }
  if (encoding_errors)
  {
    info->encoding_error_output = info->done_on_match = info->out_quiet = true;
    return false;
  }
  
  bool pending_sep = false;
  
  if (info->out_file)
  {
    print_filename_in_thread (info->filename, num_nodes_visited);
    if (filename_mask)
      pending_sep = true;
    else
      putc_errno_mthread (num_nodes_visited, 0);
  }
  
  if (out_line)
  {
    if (info->lastnl < lim)
    {
      nlscan_mthread (beg,info);
      info->totalnl = add_count (info->totalnl, 1);
      info->lastnl = lim;
    }
    if (pending_sep)
      print_sep_mthread (sep, num_nodes_visited);
    print_offset_mthread (info->totalnl, 4, line_num_color, num_nodes_visited);
    pending_sep = true;
  }
  
  if (out_byte)
  {
    uintmax_t pos = add_count (info->totalcc, beg - info->bufbeg);
    pos = dossified_pos (pos);
    if (pending_sep)
      print_sep_mthread (sep, num_nodes_visited);
    print_offset_mthread (pos, 6, byte_num_color, num_nodes_visited);
    pending_sep = true;
  }
  
  if (pending_sep)
  {
    /* This assumes sep is one column wide.
     Try doing this any other way with Unicode
     (and its combining and wide characters)
     filenames and you're wasting your efforts.  */
    if (align_tabs)
      fputs_errno_mthread (num_nodes_visited, "\t\b");
    
    print_sep_mthread (sep, num_nodes_visited);
  }
  
  return true;
}

static char *
print_line_middle (char *beg, char *lim,
                   const char *line_color, const char *match_color)
{
  size_t match_size;
  size_t match_offset;
  char *cur;
  char *mid = NULL;
  char *b;
  
  for (cur = beg;
       (cur < lim
        && ((match_offset = execute (beg, lim - beg, &match_size, cur))
            != (size_t) -1));
       cur = b + match_size)
  {
    b = beg + match_offset;
    
    /* Avoid matching the empty line at the end of the buffer. */
    if (b == lim)
      break;
    
    /* Avoid hanging on grep --color "" foo */
    if (match_size == 0)
    {
      /* Make minimal progress; there may be further non-empty matches.  */
      /* XXX - Could really advance by one whole multi-octet character.  */
      match_size = 1;
      if (!mid)
        mid = cur;
    }
    else
    {
      /* This function is called on a matching line only,
       but is it selected or rejected/context?  */
      if (only_matching)
      {
        char sep = out_invert ? SEP_CHAR_REJECTED : SEP_CHAR_SELECTED;
        if (! print_line_head (b, match_size, lim, sep))
          return NULL;
      }
      else
      {
        pr_sgr_start (line_color);
        if (mid)
        {
          cur = mid;
          mid = NULL;
        }
        fwrite_errno (cur, 1, b - cur);
      }
      
      pr_sgr_start_if (match_color);
      fwrite_errno (b, 1, match_size);
      pr_sgr_end_if (match_color);
      if (only_matching)
        putchar_errno (eolbyte);
    }
  }
  
  if (only_matching)
    cur = lim;
  else if (mid)
    cur = mid;
  
  return cur;
}

/* Multithreading version */
static char *
print_line_middle_mthread (char *beg, char *lim,
                           const char *line_color, const char *match_color, struct grep_info *info)
{
  int num_nodes_visited = thread_routine_arg_array[info->thread_id].num_nodes_visited;
  size_t match_size;
  size_t match_offset;
  char *cur;
  char *mid = NULL;
  char *b;
  
  cur = beg;
  while (cur < lim)
  {
    if (execute == EGexecute)
    {
      match_offset = EGexecute_mthread (beg, lim - beg, &match_size, cur, info->thread_id);
    }
    else
    {
      match_offset = execute (beg, lim - beg, &match_size, cur);
    }
    if (match_offset == (size_t) -1)
      break;
    
    b = beg + match_offset;
    
    /* Avoid matching the empty line at the end of the buffer. */
    if (b == lim)
      break;
    
    /* Avoid hanging on grep --color "" foo */
    if (match_size == 0)
    {
      /* Make minimal progress; there may be further non-empty matches.  */
      /* XXX - Could really advance by one whole multi-octet character.  */
      match_size = 1;
      if (!mid)
        mid = cur;
    }
    else
    {
      /* This function is called on a matching line only,
       but is it selected or rejected/context?  */
      if (only_matching)
      {
        char sep = out_invert ? SEP_CHAR_REJECTED : SEP_CHAR_SELECTED;
        if (! print_line_head_mthread (b, match_size, lim, sep, info))
          return NULL;
      }
      else
      {
        pr_sgr_start_mthread (line_color, num_nodes_visited);
        if (mid)
        {
          cur = mid;
          mid = NULL;
        }
        fwrite_errno_mthread (cur, 1, b - cur, num_nodes_visited);
      }
      
      pr_sgr_start_if_mthread (match_color, num_nodes_visited);
      fwrite_errno_mthread (b, 1, match_size, num_nodes_visited);
      pr_sgr_end_if_mthread (match_color, num_nodes_visited);
      if (only_matching)
        putc_errno_mthread (num_nodes_visited, eolbyte);
    }
    cur = b + match_size;
  }
  
  if (only_matching)
    cur = lim;
  else if (mid)
    cur = mid;
  
  return cur;
}

static char *
print_line_tail (char *beg, const char *lim, const char *line_color)
{
  size_t eol_size;
  size_t tail_size;
  
  eol_size   = (lim > beg && lim[-1] == eolbyte);
  eol_size  += (lim - eol_size > beg && lim[-(1 + eol_size)] == '\r');
  tail_size  =  lim - eol_size - beg;
  
  if (tail_size > 0)
  {
    pr_sgr_start (line_color);
    fwrite_errno (beg, 1, tail_size);
    beg += tail_size;
    pr_sgr_end (line_color);
  }
  
  return beg;
}
/* Multithreading version */
static char *
print_line_tail_mthread (char *beg, const char *lim, const char *line_color, struct grep_info *info)
{
  size_t eol_size;
  size_t tail_size;
  int num_nodes_visited = thread_routine_arg_array[info->thread_id].num_nodes_visited;
  eol_size   = (lim > beg && lim[-1] == eolbyte);
  eol_size  += (lim - eol_size > beg && lim[-(1 + eol_size)] == '\r');
  tail_size  =  lim - eol_size - beg;
  
  if (tail_size > 0)
  {
    pr_sgr_start_mthread (line_color, num_nodes_visited);
    fwrite_errno_mthread (beg, 1, tail_size, num_nodes_visited);
    beg += tail_size;
    pr_sgr_end_mthread (line_color, num_nodes_visited);
  }
  
  return beg;
}

static void
prline (char *beg, char *lim, char sep)
{
  bool matching;
  const char *line_color;
  const char *match_color;
  
  if (!only_matching)
    if (! print_line_head (beg, lim - beg - 1, lim, sep))
      return;
  
  matching = (sep == SEP_CHAR_SELECTED) ^ out_invert;
  
  if (color_option)
  {
    line_color = (((sep == SEP_CHAR_SELECTED)
                   ^ (out_invert && (color_option < 0)))
                  ? selected_line_color  : context_line_color);
    match_color = (sep == SEP_CHAR_SELECTED
                   ? selected_match_color : context_match_color);
  }
  else
    line_color = match_color = NULL; /* Shouldn't be used.  */
  
  if ((only_matching && matching)
      || (color_option && (*line_color || *match_color)))
  {
    /* We already know that non-matching lines have no match (to colorize). */
    if (matching && (only_matching || *match_color))
    {
      beg = print_line_middle (beg, lim, line_color, match_color);
      if (! beg)
        return;
    }
    
    if (!only_matching && *line_color)
    {
      /* This code is exercised at least when grep is invoked like this:
       echo k| GREP_COLORS='sl=01;32' src/grep k --color=always  */
      beg = print_line_tail (beg, lim, line_color);
    }
  }
  
  if (!only_matching && lim > beg)
    fwrite_errno (beg, 1, lim - beg);
  
  if (line_buffered)
    fflush_errno ();
  
  if (stdout_errno)
    error (EXIT_TROUBLE, stdout_errno, _("write error"));
  
  lastout = lim;
}

/* Multithreading version */
static void
prline_mthread (char *beg, char *lim, char sep, struct grep_info *info)
{
  bool matching;
  const char *line_color;
  const char *match_color;
  int num_nodes_visited = thread_routine_arg_array[info->thread_id].num_nodes_visited;
  
  if (!only_matching)
    if (! print_line_head_mthread (beg, lim - beg - 1, lim, sep, info))
      return;
  
  matching = (sep == SEP_CHAR_SELECTED) ^ out_invert;
  
  if (color_option)
  {
    line_color = (((sep == SEP_CHAR_SELECTED)
                   ^ (out_invert && (color_option < 0)))
                  ? selected_line_color  : context_line_color);
    match_color = (sep == SEP_CHAR_SELECTED
                   ? selected_match_color : context_match_color);
  }
  else
    line_color = match_color = NULL; /* Shouldn't be used.  */
  
  if ((only_matching && matching)
      || (color_option && (*line_color || *match_color)))
  {
    /* We already know that non-matching lines have no match (to colorize). */
    if (matching && (only_matching || *match_color))
    {
      beg = print_line_middle_mthread (beg, lim, line_color, match_color, info);
      if (! beg)
        return;
    }
    
    if (!only_matching && *line_color)
    {
      /* This code is exercised at least when grep is invoked like this:
       echo k| GREP_COLORS='sl=01;32' src/grep k --color=always  */
      beg = print_line_tail_mthread (beg, lim, line_color, info);
    }
  }
  
  if (!only_matching && lim > beg)
    fwrite_errno_mthread (beg, 1, lim - beg, num_nodes_visited);
  
  /*
   we never use line buffering with -r
   if (line_buffered)
   fflush_errno ();
   */
  
  if (stdout_errno)
    error (EXIT_TROUBLE, stdout_errno, _("write error"));
  
  info->lastout = lim;
}

/* Print pending lines of trailing context prior to LIM. Trailing context ends
 at the next matching line when OUTLEFT is 0.  */
static void
prpending (char const *lim)
{
  if (!lastout)
    lastout = bufbeg;
  while (pending > 0 && lastout < lim)
  {
    char *nl = memchr (lastout, eolbyte, lim - lastout);
    size_t match_size;
    --pending;
    if (outleft
        || ((execute (lastout, nl + 1 - lastout,
                      &match_size, NULL) == (size_t) -1)
            == !out_invert))
      prline (lastout, nl + 1, SEP_CHAR_REJECTED);
    else
      pending = 0;
  }
}

/* Multithreading version */
static void
prpending_mthread (char const *lim, struct grep_info *info)
{
  if (!(info->lastout))
    info->lastout = info->bufbeg;
  while (info->pending > 0 && info->lastout < lim)
  {
    char *nl = memchr (info->lastout, eolbyte, lim - info->lastout);
    size_t match_size;
    --(info->pending);
    bool temp;
    if (execute == EGexecute)
    {
      temp = EGexecute_mthread (info->lastout, nl + 1 - info->lastout, &match_size, NULL, info->thread_id) == (size_t) -1;
    }
    else
    {
      temp = execute (info->lastout, nl + 1 - info->lastout, &match_size, NULL) == (size_t) -1;
    }
    if (info->outleft || (temp == !out_invert))
    {
      prline_mthread (info->lastout, nl + 1, SEP_CHAR_REJECTED, info);
    }
    else
      info->pending = 0;
  }
}

/* Output the lines between BEG and LIM.  Deal with context.  */
static void
prtext (char *beg, char *lim)
{
  static bool used;	/* Avoid printing SEP_STR_GROUP before any output.  */
  char eol = eolbyte;
  
  if (!out_quiet && pending > 0)
    prpending (beg);
  
  char *p = beg;
  
  if (!out_quiet)
  {
    /* Deal with leading context.  */
    char const *bp = lastout ? lastout : bufbeg;
    intmax_t i;
    for (i = 0; i < out_before; ++i)
      if (p > bp)
        do
          --p;
    while (p[-1] != eol);
    
    /* Print the group separator unless the output is adjacent to
     the previous output in the file.  */
    if ((0 <= out_before || 0 <= out_after) && used
        && p != lastout && group_separator)
    {
      pr_sgr_start_if (sep_color);
      fputs_errno (group_separator);
      pr_sgr_end_if (sep_color);
      putchar_errno ('\n');
    }
    
    while (p < beg)
    {
      char *nl = memchr (p, eol, beg - p);
      nl++;
      prline (p, nl, SEP_CHAR_REJECTED);
      p = nl;
    }
  }
  
  intmax_t n;
  if (out_invert)
  {
    /* One or more lines are output.  */
    for (n = 0; p < lim && n < outleft; n++)
    {
      char *nl = memchr (p, eol, lim - p);
      nl++;
      if (!out_quiet)
        prline (p, nl, SEP_CHAR_SELECTED);
      p = nl;
    }
  }
  else
  {
    /* Just one line is output.  */
    if (!out_quiet)
      prline (beg, lim, SEP_CHAR_SELECTED);
    n = 1;
    p = lim;
  }
  
  after_last_match = bufoffset - (buflim - p);
  pending = out_quiet ? 0 : MAX (0, out_after);
  used = true;
  outleft -= n;
}

/* Multithreading version */
static void
prtext_mthread (char *beg, char *lim, struct grep_info *info)
{
  char eol = eolbyte;
  int num_nodes_visited = thread_routine_arg_array[info->thread_id].num_nodes_visited;
  if (!info->out_quiet && info->pending > 0)
    prpending_mthread (beg, info);
  
  char *p = beg;
  
  if (!info->out_quiet)
  {
    /* Deal with leading context.  */
    char const *bp = info->lastout ? info->lastout : info->bufbeg;
    intmax_t i;
    for (i = 0; i < out_before; ++i)
      if (p > bp)
        do
          --p;
    while (p[-1] != eol);
    
    /* Print the group separator unless the output is adjacent to
     the previous output in the file.  */
    if ((0 <= out_before || 0 <= out_after) && p != info->lastout && group_separator)
    {
      pr_sgr_start_if_mthread (sep_color, num_nodes_visited);
      fputs_errno_mthread (num_nodes_visited, group_separator);
      pr_sgr_end_if_mthread (sep_color, num_nodes_visited);
      putc_errno_mthread (num_nodes_visited, '\n');
    }
    while (p < beg)
    {
      char *nl = memchr (p, eol, beg - p);
      nl++;
      prline_mthread (p, nl, SEP_CHAR_REJECTED, info);
      p = nl;
    }
  }
  
  intmax_t n;
  if (out_invert)
  {
    /* One or more lines are output.  */
    for (n = 0; p < lim && n < info->outleft; n++)
    {
      char *nl = memchr (p, eol, lim - p);
      nl++;
      if (!info->out_quiet)
        prline_mthread (p, nl, SEP_CHAR_SELECTED, info);
      p = nl;
    }
  }
  else
  {
    /* Just one line is output.  */
    if (!info->out_quiet)
      prline_mthread (beg, lim, SEP_CHAR_SELECTED, info);
    n = 1;
    p = lim;
  }
  
  info->after_last_match = info->bufoffset - (info->buflim - p);
  info->pending = info->out_quiet ? 0 : MAX (0, out_after);
  info->outleft -= n;
}

/* Replace all NUL bytes in buffer P (which ends at LIM) with EOL.
 This avoids running out of memory when binary input contains a long
 sequence of zeros, which would otherwise be considered to be part
 of a long line.  P[LIM] should be EOL.  */
static void
zap_nuls (char *p, char *lim, char eol)
{
  if (eol)
    while (true)
    {
      *lim = '\0';
      p += strlen (p);
      *lim = eol;
      if (p == lim)
        break;
      do
        *p++ = eol;
      while (!*p);
    }
}

/* Scan the specified portion of the buffer, matching lines (or
 between matching lines if OUT_INVERT is true).  Return a count of
 lines printed.  Replace all NUL bytes with NUL_ZAPPER as we go.  */
static intmax_t
grepbuf (char *beg, char const *lim)
{
  intmax_t outleft0 = outleft;
  char *endp;
  
  for (char *p = beg; p < lim; p = endp)
  {
    size_t match_size;
    size_t match_offset = execute (p, lim - p, &match_size, NULL);
    if (match_offset == (size_t) -1)
    {
      if (!out_invert)
        break;
      match_offset = lim - p;
      match_size = 0;
    }
    char *b = p + match_offset;
    endp = b + match_size;
    /* Avoid matching the empty line at the end of the buffer. */
    if (!out_invert && b == lim)
      break;
    if (!out_invert || p < b)
    {
      char *prbeg = out_invert ? p : b;
      char *prend = out_invert ? b : endp;
      prtext (prbeg, prend);
      if (!outleft || done_on_match)
      {
        if (exit_on_match)
          exit (errseen ? exit_failure : EXIT_SUCCESS);
        break;
      }
    }
  }
  
  return outleft0 - outleft;
}

/* Multithreading version */
static intmax_t
grepbuf_mthread (char *beg, char const *lim, struct grep_info *info)
{
  intmax_t outleft0 = info->outleft;
  char *endp;
  
  for (char *p = beg; p < lim; p = endp)
  {
    size_t match_size;
    size_t match_offset;
    if (execute == EGexecute)
    {
      match_offset = EGexecute_mthread (p, lim - p, &match_size, NULL, info->thread_id);
    }
    else
    {
      match_offset = execute (p, lim - p, &match_size, NULL);
    }
    
    if (match_offset == (size_t) -1)
    {
      if (!out_invert)
        break;
      match_offset = lim - p;
      match_size = 0;
    }
    char *b = p + match_offset;
    endp = b + match_size;
    /* Avoid matching the empty line at the end of the buffer. */
    if (!out_invert && b == lim)
      break;
    if (!out_invert || p < b)
    {
      char *prbeg = out_invert ? p : b;
      char *prend = out_invert ? b : endp;
      
      prtext_mthread (prbeg, prend, info);
      
      if (!(info->outleft) || info->done_on_match)
      {
        if (exit_on_match)
          exit (errseen ? exit_failure : EXIT_SUCCESS);
        break;
      }
    }
  }
  
  return outleft0 - info->outleft;
}

/* Search a given (non-directory) file.  Return a count of lines printed. */
static intmax_t
grep (int fd, struct stat const *st)
{
  intmax_t nlines, i;
  size_t residue, save;
  char oldc;
  char *beg;
  char *lim;
  char eol = eolbyte;
  char nul_zapper = '\0';
  bool done_on_match_0 = done_on_match;
  bool out_quiet_0 = out_quiet;
  
  /* The value of NLINES when nulls were first deduced in the input;
   this is not necessarily the same as the number of matching lines
   before the first null.  -1 if no input nulls have been deduced.  */
  intmax_t nlines_first_null = -1;
  
  if (! reset (fd, st))
    return 0;
  
  totalcc = 0;
  lastout = 0;
  totalnl = 0;
  outleft = max_count;
  after_last_match = 0;
  pending = 0;
  skip_nuls = skip_empty_lines && !eol;
  encoding_error_output = false;
  seek_data_failed = false;
  
  nlines = 0;
  residue = 0;
  save = 0;
  
  if (! fillbuf (save, st))
  {
    suppressible_error (filename, errno);
    return 0;
  }
  
  for (bool firsttime = true; ; firsttime = false)
  {
    if (nlines_first_null < 0 && eol && binary_files != TEXT_BINARY_FILES
        && (buf_has_nulls (bufbeg, buflim - bufbeg)
            || (firsttime && file_must_have_nulls (buflim - bufbeg, fd, st))))
    {
      if (binary_files == WITHOUT_MATCH_BINARY_FILES)
        return 0;
      if (!count_matches)
        done_on_match = out_quiet = true;
      nlines_first_null = nlines;
      nul_zapper = eol;
      skip_nuls = skip_empty_lines;
    }
    
    lastnl = bufbeg;
    if (lastout)
      lastout = bufbeg;
    
    beg = bufbeg + save;
    
    /* no more data to scan (eof) except for maybe a residue -> break */
    if (beg == buflim)
      break;
    
    zap_nuls (beg, buflim, nul_zapper);
    
    /* Determine new residue (the length of an incomplete line at the end of
     the buffer, 0 means there is no incomplete last line).  */
    oldc = beg[-1];
    beg[-1] = eol;
    /* FIXME: use rawmemrchr if/when it exists, since we have ensured
     that this use of memrchr is guaranteed never to return NULL.  */
    lim = memrchr (beg - 1, eol, buflim - beg + 1);
    ++lim;
    beg[-1] = oldc;
    if (lim == beg)
      lim = beg - residue;
    beg -= residue;
    residue = buflim - lim;
    
    if (beg < lim)
    {
      if (outleft)
        nlines += grepbuf (beg, lim);
      if (pending)
        prpending (lim);
      if ((!outleft && !pending)
          || (done_on_match && MAX (0, nlines_first_null) < nlines))
        goto finish_grep;
    }
    
    /* The last OUT_BEFORE lines at the end of the buffer will be needed as
     leading context if there is a matching line at the begin of the
     next data. Make beg point to their begin.  */
    i = 0;
    beg = lim;
    while (i < out_before && beg > bufbeg && beg != lastout)
    {
      ++i;
      do
        --beg;
      while (beg[-1] != eol);
    }
    
    /* Detect whether leading context is adjacent to previous output.  */
    if (beg != lastout)
      lastout = 0;
    
    /* Handle some details and read more data to scan.  */
    save = residue + lim - beg;
    if (out_byte)
      totalcc = add_count (totalcc, buflim - bufbeg - save);
    if (out_line)
      nlscan (beg);
    if (! fillbuf (save, st))
    {
      suppressible_error (filename, errno);
      goto finish_grep;
    }
  }
  if (residue)
  {
    *buflim++ = eol;
    if (outleft)
      nlines += grepbuf (bufbeg + save - residue, buflim);
    if (pending)
      prpending (buflim);
  }
  
finish_grep:
  done_on_match = done_on_match_0;
  out_quiet = out_quiet_0;
  if (!out_quiet && (encoding_error_output
                     || (0 <= nlines_first_null && nlines_first_null < nlines)))
  {
    printf_errno (_("Binary file %s matches\n"), filename);
    if (line_buffered)
      fflush_errno ();
  }
  return nlines;
}

/* Multithreaing version */
static intmax_t
grep_mthread (int fd, struct stat const *st, struct grep_info *info)
{
  intmax_t nlines, i;
  size_t residue, save;
  char oldc;
  char *beg;
  char *lim;
  char eol = eolbyte;
  char nul_zapper = '\0';
  bool done_on_match_0 = info->done_on_match;
  bool out_quiet_0 = info->out_quiet;
  int thread_id = info->thread_id;
  int num_nodes_visited = thread_routine_arg_array[thread_id].num_nodes_visited;
  
  /* The value of NLINES when nulls were first deduced in the input;
   this is not necessarily the same as the number of matching lines
   before the first null.  -1 if no input nulls have been deduced.  */
  intmax_t nlines_first_null = -1;
  
  if (! reset_mthread (fd, st, info))
    return 0;
  
  info -> totalcc = 0;
  info -> lastout = 0;
  info -> totalnl = 0;
  info -> outleft = max_count;
  info -> after_last_match = 0;
  info -> pending = 0;
  info -> skip_nuls = info->skip_empty_lines && !eol;
  info -> encoding_error_output = false;
  info -> seek_data_failed = false;
  
  nlines = 0;
  residue = 0;
  save = 0;
  
  if (! fillbuf_mthread (save, st, info))
  {
    suppressible_error (info->filename, errno);
    return 0;
  }
  for (bool firsttime = true; ; firsttime = false)
  {
    if (nlines_first_null < 0 && eol && binary_files != TEXT_BINARY_FILES
        && (buf_has_nulls (info->bufbeg, info->buflim - info->bufbeg)
            || (firsttime && file_must_have_nulls_mthread (info->buflim - info->bufbeg, fd, st, info))))
    {
      if (binary_files == WITHOUT_MATCH_BINARY_FILES)
        return 0;
      if (!count_matches)
        info->done_on_match = info->out_quiet = true;
      nlines_first_null = nlines;
      nul_zapper = eol;
      info->skip_nuls = info->skip_empty_lines;
    }
    
    info->lastnl = info->bufbeg;
    if (info->lastout)
      info->lastout = info->bufbeg;
    
    beg = info->bufbeg + save;
    
    /* no more data to scan (eof) except for maybe a residue -> break */
    if (beg == info->buflim)
      break;
    
    zap_nuls (beg, info->buflim, nul_zapper);
    
    /* Determine new residue (the length of an incomplete line at the end of
     the buffer, 0 means there is no incomplete last line).  */
    oldc = beg[-1];
    beg[-1] = eol;
    /* FIXME: use rawmemrchr if/when it exists, since we have ensured
     that this use of memrchr is guaranteed never to return NULL.  */
    lim = memrchr (beg - 1, eol, info->buflim - beg + 1);
    ++lim;
    beg[-1] = oldc;
    if (lim == beg)
      lim = beg - residue;
    beg -= residue;
    residue = info->buflim - lim;
    
    if (beg < lim)
    {
      if (info->outleft)
        nlines += grepbuf_mthread (beg, lim, info);
      if (info->pending)
        prpending_mthread (lim, info);
      if ((!info->outleft && !info->pending)
          || (info->done_on_match && MAX (0, nlines_first_null) < nlines))
        goto finish_grep;
    }
    
    /* The last OUT_BEFORE lines at the end of the buffer will be needed as
     leading context if there is a matching line at the begin of the
     next data. Make beg point to their begin.  */
    i = 0;
    beg = lim;
    while (i < out_before && beg > info->bufbeg && beg != info->lastout)
    {
      ++i;
      do
        --beg;
      while (beg[-1] != eol);
    }
    
    /* Detect whether leading context is adjacent to previous output.  */
    if (beg != info->lastout)
      info->lastout = 0;
    
    /* Handle some details and read more data to scan.  */
    save = residue + lim - beg;
    if (out_byte)
      info->totalcc = add_count (info->totalcc, info->buflim - info->bufbeg - save);
    if (out_line)
      nlscan_mthread (beg, info);
    if (! fillbuf_mthread (save, st, info))
    {
      suppressible_error (info->filename, errno);
      goto finish_grep;
    }
  }
  if (residue)
  {
    *(info->buflim)++ = eol;
    if (info->outleft)
      nlines += grepbuf_mthread (info->bufbeg + save - residue, info->buflim, info);
    if (info->pending)
      prpending_mthread (info->buflim, info);
  }
  
finish_grep:
  info->done_on_match = done_on_match_0;
  info->out_quiet = out_quiet_0;
  if (!info->out_quiet && (info->encoding_error_output
                           || (0 <= nlines_first_null && nlines_first_null < nlines)))
  {
    printf_errno_mthread (num_nodes_visited, strlen (info->filename) + 30 ,_("Binary file %s matches\n"), info->filename);
    /*
     we never use line buffering with -r
     if (line_buffered)
     fflush_errno ();
     */
  }
  
  return nlines;
}

static bool
grepdirent (FTS *fts, FTSENT *ent, bool command_line)
{
  bool follow;
  command_line &= ent->fts_level == FTS_ROOTLEVEL;
  
  if (ent->fts_info == FTS_DP)
  {
    if (directories == RECURSE_DIRECTORIES && command_line)
      out_file &= ~ (2 * !no_filenames);
    return true;
  }
  
  if (!command_line
      && skipped_file (ent->fts_name, false,
                       (ent->fts_info == FTS_D || ent->fts_info == FTS_DC
                        || ent->fts_info == FTS_DNR)))
  {
    fts_set (fts, ent, FTS_SKIP);
    return true;
  }
  
  filename = ent->fts_path;
  if (omit_dot_slash && filename[1])
    filename += 2;
  follow = (fts->fts_options & FTS_LOGICAL
            || (fts->fts_options & FTS_COMFOLLOW && command_line));
  
  switch (ent->fts_info)
  {
    case FTS_D:
      if (directories == RECURSE_DIRECTORIES)
      {
        out_file |= 2 * !no_filenames;
        return true;
      }
      fts_set (fts, ent, FTS_SKIP);
      break;
      
    case FTS_DC:
      if (!suppress_errors)
        error (0, 0, _("warning: %s: %s"), filename,
               _("recursive directory loop"));
      return true;
      
    case FTS_DNR:
    case FTS_ERR:
    case FTS_NS:
      suppressible_error (filename, ent->fts_errno);
      return true;
      
    case FTS_DEFAULT:
    case FTS_NSOK:
      if (skip_devices (command_line))
      {
        struct stat *st = ent->fts_statp;
        struct stat st1;
        if (! st->st_mode)
        {
          /* The file type is not already known.  Get the file status
           before opening, since opening might have side effects
           on a device.  */
          int flag = follow ? 0 : AT_SYMLINK_NOFOLLOW;
          if (fstatat (fts->fts_cwd_fd, ent->fts_accpath, &st1, flag) != 0)
          {
            suppressible_error (filename, errno);
            return true;
          }
          st = &st1;
        }
        if (is_device_mode (st->st_mode))
          return true;
      }
      break;
      
    case FTS_F:
    case FTS_SLNONE:
      break;
      
    case FTS_SL:
    case FTS_W:
      return true;
      
    default:
      abort ();
  }
  
  return grepfile (fts->fts_cwd_fd, ent->fts_accpath, follow, command_line);
}

void *
thread_routine(void *arg){
  int thread_id = ((struct thread_routine_arg *)arg)->thread_id;
  int *num_nodes_visited = &((struct thread_routine_arg *)arg)->num_nodes_visited;
  intmax_t *current_max_num_nodes_addr = &((struct thread_routine_arg *)arg)->current_max_num_nodes;
  /* make the variables local */
  intmax_t max_allowed_num_nodes_local = max_allowed_num_nodes;
  int num_threads_local = num_threads;
  
  bool has_entry = true;
  FTSENT *ent;
  has_entry = (ent = fts_read (fts_global_array[thread_id]));
  while (has_entry)
  {
    bool follow;
    thread_routine_arg_array[thread_id].command_line_local &= ent->fts_level == FTS_ROOTLEVEL;
    
    if (ent->fts_info == FTS_DP)
    {
      if (thread_routine_arg_array[thread_id].command_line_local)
        grep_info_array[thread_id].out_file &= ~ (2 * !(thread_routine_arg_array[thread_id].no_filenames));
      if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
      {
        lock_buffer_locks();
        raise_max_nodes (*num_nodes_visited);
        unlock_buffer_locks();
      }
      *num_nodes_visited += 1;
      if (*num_nodes_visited >= max_allowed_num_nodes_local)
      {
        return NULL;
      }
      has_entry = (ent = fts_read (fts_global_array[thread_id]));
      continue;
    }
    
    if (!thread_routine_arg_array[thread_id].command_line_local
        && skipped_file (ent->fts_name, false,
                         (ent->fts_info == FTS_D || ent->fts_info == FTS_DC
                          || ent->fts_info == FTS_DNR)))
    {
      fts_set (fts_global_array[thread_id], ent, FTS_SKIP);
      if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
      {
        lock_buffer_locks();
        raise_max_nodes (*num_nodes_visited);
        unlock_buffer_locks();
      }
      *num_nodes_visited += 1;
      if (*num_nodes_visited >= max_allowed_num_nodes_local)
      {
        return NULL;
      }
      has_entry = (ent = fts_read (fts_global_array[thread_id]));
      continue;
    }
    
    thread_routine_arg_array[thread_id].filename_local = ent->fts_path;
    if (omit_dot_slash && (thread_routine_arg_array[thread_id].filename_local)[1])
      thread_routine_arg_array[thread_id].filename_local += 2;
    follow = (fts_global_array[thread_id]->fts_options & FTS_LOGICAL
              || (fts_global_array[thread_id]->fts_options & FTS_COMFOLLOW
                  && thread_routine_arg_array[thread_id].command_line_local));
    
    switch (ent->fts_info)
    {
      case FTS_D:
        grep_info_array[thread_id].out_file |= 2 * !(thread_routine_arg_array[thread_id].no_filenames);
        if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
        {
          lock_buffer_locks();
          raise_max_nodes (*num_nodes_visited);
          unlock_buffer_locks();
        }
        *num_nodes_visited += 1;
        if (*num_nodes_visited >= max_allowed_num_nodes_local)
        {
          return NULL;
        }
        has_entry = (ent = fts_read (fts_global_array[thread_id]));
        continue;
        
      case FTS_DC:
        if (!suppress_errors)
          error (0, 0, _("warning: %s: %s"), thread_routine_arg_array[thread_id].filename_local,
                 _("recursive directory loop"));
        if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
        {
          lock_buffer_locks();
          raise_max_nodes (*num_nodes_visited);
          unlock_buffer_locks();
        }
        *num_nodes_visited += 1;
        if (*num_nodes_visited >= max_allowed_num_nodes_local)
        {
          return NULL;
        }
        has_entry = (ent = fts_read (fts_global_array[thread_id]));
        continue;
        
      case FTS_DNR:
      case FTS_ERR:
      case FTS_NS:
        suppressible_error (thread_routine_arg_array[thread_id].filename_local, ent->fts_errno);
        if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
        {
          lock_buffer_locks();
          raise_max_nodes (*num_nodes_visited);
          unlock_buffer_locks();
        }
        *num_nodes_visited += 1;
        if (*num_nodes_visited >= max_allowed_num_nodes_local)
        {
          return NULL;
        }
        has_entry = (ent = fts_read (fts_global_array[thread_id]));
        continue;
        
      case FTS_DEFAULT:
      case FTS_NSOK:
        if (skip_devices (thread_routine_arg_array[thread_id].command_line_local))
        {
          struct stat *st = ent->fts_statp;
          struct stat st1;
          if (! st->st_mode)
          {
            /* The file type is not already known.  Get the file status
             before opening, since opening might have side effects
             on a device.  */
            int flag = follow ? 0 : AT_SYMLINK_NOFOLLOW;
            if (fstatat (fts_global_array[thread_id]->fts_cwd_fd, ent->fts_accpath, &st1, flag) != 0)
            {
              suppressible_error (thread_routine_arg_array[thread_id].filename_local, errno);
              if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
              {
                lock_buffer_locks();
                raise_max_nodes (*num_nodes_visited);
                unlock_buffer_locks();
              }
              *num_nodes_visited += 1;
              if (*num_nodes_visited >= max_allowed_num_nodes_local)
              {
                return NULL;
              }
              has_entry = (ent = fts_read (fts_global_array[thread_id]));
              continue;
            }
            st = &st1;
          }
          if (is_device_mode (st->st_mode)){
            if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
            {
              lock_buffer_locks();
              raise_max_nodes (*num_nodes_visited);
              unlock_buffer_locks();
            }
            *num_nodes_visited += 1;
            if (*num_nodes_visited >= max_allowed_num_nodes_local)
            {
              return NULL;
            }
            has_entry = (ent = fts_read (fts_global_array[thread_id]));
            continue;
          }
        }
        break;
        
      case FTS_F:
      case FTS_SLNONE:
        break;
        
      case FTS_SL:
      case FTS_W:
        if (*num_nodes_visited % num_threads_local == thread_id && *num_nodes_visited > *current_max_num_nodes_addr - 4)
        {
          lock_buffer_locks();
          raise_max_nodes (*num_nodes_visited);
          unlock_buffer_locks();
        }
        *num_nodes_visited += 1;
        if (*num_nodes_visited >= max_allowed_num_nodes_local)
        {
          return NULL;
        }
        has_entry = (ent = fts_read (fts_global_array[thread_id]));
        continue;
        
      default:
        abort ();
    }
    
    if (*num_nodes_visited % num_threads_local == thread_id)
    {
      if (*num_nodes_visited > *current_max_num_nodes_addr - 4)
      {
        lock_buffer_locks();
        raise_max_nodes (*num_nodes_visited);
        unlock_buffer_locks();
      }
      status_array[thread_id] &=
      grepfile_mthread (fts_global_array[thread_id]->fts_cwd_fd, ent->fts_accpath, follow,
                        thread_routine_arg_array[thread_id].command_line_local, thread_id);
    }
    *num_nodes_visited += 1;
    if (*num_nodes_visited >= max_allowed_num_nodes_local)
    {
      return NULL;
    }
    has_entry = (ent = fts_read (fts_global_array[thread_id]));
  }
  if (thread_id == 0)
    recur = false;
  return NULL;
}

/* True if errno is ERR after 'open ("symlink", ... O_NOFOLLOW ...)'.
 POSIX specifies ELOOP, but it's EMLINK on FreeBSD and EFTYPE on NetBSD.  */
static bool
open_symlink_nofollow_error (int err)
{
  if (err == ELOOP || err == EMLINK)
    return true;
#ifdef EFTYPE
  if (err == EFTYPE)
    return true;
#endif
  return false;
}

static bool
grepfile (int dirdesc, char const *name, bool follow, bool command_line)
{
  int oflag = (O_RDONLY | O_NOCTTY
               | (follow ? 0 : O_NOFOLLOW)
               | (skip_devices (command_line) ? O_NONBLOCK : 0));
  int desc = openat_safer (dirdesc, name, oflag);
  if (desc < 0)
  {
    if (follow || ! open_symlink_nofollow_error (errno))
      suppressible_error (filename, errno);
    return true;
  }
  return grepdesc (desc, command_line);
}
/* multithreading version */
static bool
grepfile_mthread (int dirdesc, char const *name, bool follow, bool command_line, int thread_id)
{
  int oflag = (O_RDONLY | O_NOCTTY
               | (follow ? 0 : O_NOFOLLOW)
               | (skip_devices (command_line) ? O_NONBLOCK : 0));
  int desc = openat_safer (dirdesc, name, oflag);
  if (desc < 0)
  {
    if (follow || ! open_symlink_nofollow_error (errno))
      suppressible_error (thread_routine_arg_array[thread_id].filename_local, errno);
    return true;
  }
  return grepdesc_mthread (desc, command_line, thread_id);
}

/* to be used before calling grep */
void initialize_grep_info(struct grep_info *info){
  info -> done_on_match    = done_on_match;
  info -> out_quiet        = out_quiet;
  info -> totalcc          = 0;
  info -> lastout          = 0;
  info -> outleft          = max_count;
  info -> after_last_match = 0;
  info -> pending          = 0;
  info -> encoding_error_output = false;
  info -> seek_data_failed = false;
  info -> filename         = filename;
  info -> totalnl          = 0;
  info -> out_file         = out_file;
  info -> bufalloc         = bufalloc;
  info -> pagesize         = pagesize;
  info -> buffer           = xmalloc (bufalloc);
  info -> skip_empty_lines = skip_empty_lines;
}

/* Used for multithreading recursive grep */
static bool grepdesc_traversal_mthread (int desc, bool command_line){
  /* Traverse the directory starting with its full name, because
   unfortunately fts provides no way to traverse the directory
   starting from its file descriptor.  */
  bool status = true;
  int opts = fts_options & ~(command_line ? 0 : FTS_COMFOLLOW);
  char *fts_arg[2];
  
  /* Close DESC now, to conserve file descriptors if the race
   condition occurs many times in a deep recursion.  */
  if (close (desc) != 0)
    suppressible_error (filename, errno);
  fts_global_array = (FTS **) malloc (num_threads * sizeof (FTS *));
  fts_arg[0] = (char *) filename;
  fts_arg[1] = NULL;
  
  status_array = (bool *) malloc (num_threads * sizeof (bool));
  threads = (pthread_t *) malloc (num_threads * sizeof (pthread_t));
  thread_routine_arg_array = (struct thread_routine_arg *) malloc (num_threads * sizeof (struct thread_routine_arg));
  grep_info_array = (struct grep_info *) malloc (num_threads * sizeof (struct grep_info));
  output_buffer = (struct output_buffer_node *) malloc (initial_num_nodes * sizeof (struct output_buffer_node));
  current_max_num_nodes = initial_num_nodes;
  buffer_lock = (pthread_mutex_t *) malloc (num_threads * sizeof (pthread_mutex_t));
  for (int i=0; i<initial_num_nodes; ++i)
  {
    output_buffer[i].max_length = 0;
    output_buffer[i].actual_length = 0;
  }
  for(int i=0; i<num_threads; ++i)
  {
    pthread_mutex_init (buffer_lock + i, NULL);
    initialize_grep_info (grep_info_array+i);
    fts_global_array[i] = fts_open (fts_arg, opts, NULL);
    if (!fts_global_array[i])
      xalloc_die ();
  }
  for (int i=0; i<num_threads; ++i)
  {
    status_array[i] = true;
    thread_routine_arg_array[i].command_line_local = true;
    thread_routine_arg_array[i].no_filenames = no_filenames;
    thread_routine_arg_array[i].thread_id = i;
    thread_routine_arg_array[i].num_nodes_visited = 0;
    thread_routine_arg_array[i].current_max_num_nodes = current_max_num_nodes;
    grep_info_array[i].thread_id = i;
    pthread_create (&threads[i], NULL, thread_routine,
                    (void *) &thread_routine_arg_array[i]);
  }
  for (int i=0; i<num_threads; ++i)
  {
    pthread_join (threads[i], NULL);
  }
  
  while (recur)
  {
    int num_nodes_visited = thread_routine_arg_array[0].num_nodes_visited;
    for(int i=0; i<num_nodes_visited; ++i)
    {
      int length = output_buffer[i].actual_length;
      if (length > 0)
      {
        fwrite (output_buffer[i].content, 1, length, stdout);
        free (output_buffer[i].content);
        output_buffer[i].max_length = output_buffer[i].actual_length = 0;
      }
    }
    for (int i=0; i<num_threads; ++i)
    {
      thread_routine_arg_array[i].num_nodes_visited = 0;
      pthread_create (&threads[i], NULL, thread_routine,
                      (void *) &thread_routine_arg_array[i]);
    }
    for (int i=0; i<num_threads; ++i)
    {
      pthread_join (threads[i], NULL);
    }
  }
  int num_nodes_visited = thread_routine_arg_array[0].num_nodes_visited;
  for(int i=0; i<num_nodes_visited; ++i)
  {
    int length = output_buffer[i].actual_length;
    if (length > 0)
    {
      fwrite (output_buffer[i].content, 1, length, stdout);
      free (output_buffer[i].content);
    }
  }
  for (int i=0; i<num_threads; ++i)
  {
    status &= status_array[i];
    if (fts_close (fts_global_array[i]) != 0)
      suppressible_error (filename, errno);
  }
  free (threads);
  free (status_array);
  free (grep_info_array);
  free (thread_routine_arg_array);
  free (output_buffer);
  free (buffer_lock);
  /* FIXME: should this still be here? */
  //        if (errno)
  //            suppressible_error (filename, errno);
  return status;
}

static bool
grepdesc (int desc, bool command_line)
{
  intmax_t count;
  bool status = true;
  struct stat st;
  
  /* Get the file status, possibly for the second time.  This catches
   a race condition if the directory entry changes after the
   directory entry is read and before the file is opened.  For
   example, normally DESC is a directory only at the top level, but
   there is an exception if some other process substitutes a
   directory for a non-directory while 'grep' is running.  */
  if (fstat (desc, &st) != 0)
  {
    suppressible_error (filename, errno);
    goto closeout;
  }
  
  if (desc != STDIN_FILENO && skip_devices (command_line)
      && is_device_mode (st.st_mode))
    goto closeout;
  
  if (desc != STDIN_FILENO && command_line
      && skipped_file (filename, true, S_ISDIR (st.st_mode) != 0))
    goto closeout;
  
  if (desc != STDIN_FILENO
      && directories == RECURSE_DIRECTORIES && S_ISDIR (st.st_mode))
  {
    if (parallel) return grepdesc_traversal_mthread (desc, command_line);
    else
    {
      /* Traverse the directory starting with its full name, because
       unfortunately fts provides no way to traverse the directory
       starting from its file descriptor.  */
      
      FTS *fts;
      FTSENT *ent;
      int opts = fts_options & ~(command_line ? 0 : FTS_COMFOLLOW);
      char *fts_arg[2];
      
      /* Close DESC now, to conserve file descriptors if the race
       condition occurs many times in a deep recursion.  */
      if (close (desc) != 0)
        suppressible_error (filename, errno);
      
      fts_arg[0] = (char *) filename;
      fts_arg[1] = NULL;
      fts = fts_open (fts_arg, opts, NULL);
      
      if (!fts)
        xalloc_die ();
      
      while ((ent = fts_read (fts))){
        status &= grepdirent (fts, ent, command_line);
      }
      if (errno)
        suppressible_error (filename, errno);
      if (fts_close (fts) != 0)
        suppressible_error (filename, errno);
      return status;
    }
  }
  
  if (desc != STDIN_FILENO
      && ((directories == SKIP_DIRECTORIES && S_ISDIR (st.st_mode))
          || ((devices == SKIP_DEVICES
               || (devices == READ_COMMAND_LINE_DEVICES && !command_line))
              && is_device_mode (st.st_mode))))
    goto closeout;
  
  /* If there is a regular file on stdout and the current file refers
   to the same i-node, we have to report the problem and skip it.
   Otherwise when matching lines from some other input reach the
   disk before we open this file, we can end up reading and matching
   those lines and appending them to the file from which we're reading.
   Then we'd have what appears to be an infinite loop that'd terminate
   only upon filling the output file system or reaching a quota.
   However, there is no risk of an infinite loop if grep is generating
   no output, i.e., with --silent, --quiet, -q.
   Similarly, with any of these:
   --max-count=N (-m) (for N >= 2)
   --files-with-matches (-l)
   --files-without-match (-L)
   there is no risk of trouble.
   For --max-count=1, grep stops after printing the first match,
   so there is no risk of malfunction.  But even --max-count=2, with
   input==output, while there is no risk of infloop, there is a race
   condition that could result in "alternate" output.  */
  if (!out_quiet && list_files == LISTFILES_NONE && 1 < max_count
      && SAME_INODE (st, out_stat))
  {
    if (! suppress_errors)
      error (0, 0, _("input file %s is also the output"), quote (filename));
    errseen = true;
    goto closeout;
  }
  
#if defined SET_BINARY
  /* Set input to binary mode.  Pipes are simulated with files
   on DOS, so this includes the case of "foo | grep bar".  */
  if (!isatty (desc))
    SET_BINARY (desc);
#endif
  
  count = grep (desc, &st);
  if (count_matches)
  {
    if (out_file)
    {
      print_filename ();
      if (filename_mask)
        print_sep (SEP_CHAR_SELECTED);
      else
        putchar_errno (0);
    }
    printf_errno ("%" PRIdMAX "\n", count);
    if (line_buffered)
      fflush_errno ();
  }
  
  status = !count;
  if (list_files == (status ? LISTFILES_NONMATCHING : LISTFILES_MATCHING))
  {
    print_filename ();
    putchar_errno ('\n' & filename_mask);
    if (line_buffered)
      fflush_errno ();
  }
  
  if (desc == STDIN_FILENO)
  {
    off_t required_offset = outleft ? bufoffset : after_last_match;
    if (required_offset != bufoffset
        && lseek (desc, required_offset, SEEK_SET) < 0
        && S_ISREG (st.st_mode))
      suppressible_error (filename, errno);
  }
  
closeout:
  if (desc != STDIN_FILENO && close (desc) != 0)
    suppressible_error (filename, errno);
  return status;
}

/* Multithreading version */
static bool
grepdesc_mthread (int desc, bool command_line, int thread_id)
{
  intmax_t count;
  bool status = true;
  struct stat st;
  int num_nodes_visited = thread_routine_arg_array[thread_id].num_nodes_visited;
  
  /* Get the file status, possibly for the second time.  This catches
   a race condition if the directory entry changes after the
   directory entry is read and before the file is opened.  For
   example, normally DESC is a directory only at the top level, but
   there is an exception if some other process substitutes a
   directory for a non-directory while 'grep' is running.  */
  if (fstat (desc, &st) != 0)
  {
    suppressible_error (grep_info_array[thread_id].filename, errno);
    goto closeout;
  }
  
  if (desc != STDIN_FILENO && skip_devices (command_line)
      && is_device_mode (st.st_mode)){
    goto closeout;
  }
  
  if (desc != STDIN_FILENO && command_line
      && skipped_file (grep_info_array[thread_id].filename, true, S_ISDIR (st.st_mode) != 0)){
    goto closeout;
  }
  
  if (desc != STDIN_FILENO
      && ((directories == SKIP_DIRECTORIES && S_ISDIR (st.st_mode))
          || ((devices == SKIP_DEVICES
               || (devices == READ_COMMAND_LINE_DEVICES && !command_line))
              && is_device_mode (st.st_mode))))
    goto closeout;
  
  /* If there is a regular file on stdout and the current file refers
   to the same i-node, we have to report the problem and skip it.
   Otherwise when matching lines from some other input reach the
   disk before we open this file, we can end up reading and matching
   those lines and appending them to the file from which we're reading.
   Then we'd have what appears to be an infinite loop that'd terminate
   only upon filling the output file system or reaching a quota.
   However, there is no risk of an infinite loop if grep is generating
   no output, i.e., with --silent, --quiet, -q.
   Similarly, with any of these:
   --max-count=N (-m) (for N >= 2)
   --files-with-matches (-l)
   --files-without-match (-L)
   there is no risk of trouble.
   For --max-count=1, grep stops after printing the first match,
   so there is no risk of malfunction.  But even --max-count=2, with
   input==output, while there is no risk of infloop, there is a race
   condition that could result in "alternate" output.  */
  if (!out_quiet && list_files == LISTFILES_NONE && 1 < max_count
      && SAME_INODE (st, out_stat))
  {
    if (! suppress_errors)
      error (0, 0, _("input file %s is also the output"), quote (grep_info_array[thread_id].filename));
    errseen = true;
    goto closeout;
  }
  
#if defined SET_BINARY
  /* Set input to binary mode.  Pipes are simulated with files
   on DOS, so this includes the case of "foo | grep bar".  */
  if (!isatty (desc))
    SET_BINARY (desc);
#endif
  grep_info_array[thread_id].filename = thread_routine_arg_array[thread_id].filename_local;
  
  count = grep_mthread (desc, &st, &grep_info_array[thread_id]);
  
  if (count_matches)
  {
    if (grep_info_array[thread_id].out_file)
    {
      print_filename_in_thread (grep_info_array[thread_id].filename, num_nodes_visited);
      if (filename_mask)
        print_sep_mthread (SEP_CHAR_SELECTED, num_nodes_visited);
      else
        putc_errno_mthread(num_nodes_visited, 0);
    }
    int count_length = 4, count_temp = count;
    while (count_temp != 0)
    {
      ++count_length;
      count_temp /= 10;
    }
    printf_errno_mthread (num_nodes_visited, count_length, "%" PRIdMAX "\n", count);
    /*
     we never use line buffering with -r
     if (line_buffered)
     fflush_errno ();
     */
  }
  
  status = !count;
  if (list_files == (status ? LISTFILES_NONMATCHING : LISTFILES_MATCHING))
  {
    print_filename_in_thread (grep_info_array[thread_id].filename, num_nodes_visited);
    putc_errno_mthread (num_nodes_visited, '\n' & filename_mask);
    /*
     we never use line buffering with -r
     if (line_buffered)
     fflush_errno ();
     */
  }
  
closeout:
  if (desc != STDIN_FILENO && close (desc) != 0)
    suppressible_error (thread_routine_arg_array[thread_id].filename_local, errno);
  return status;
}

static bool
grep_command_line_arg (char const *arg)
{
  if (STREQ (arg, "-"))
  {
    filename = label ? label : _("(standard input)");
    return grepdesc (STDIN_FILENO, true);
  }
  else
  {
    filename = arg;
    return grepfile (AT_FDCWD, arg, true, true);
  }
}

_Noreturn void usage (int);
void
usage (int status)
{
  if (status != 0)
  {
    fprintf (stderr, _("Usage: %s [OPTION]... PATTERN [FILE]...\n"),
             getprogname());
    fprintf (stderr, _("Try '%s --help' for more information.\n"),
             getprogname());
  }
  else
  {
    printf (_("Usage: %s [OPTION]... PATTERN [FILE]...\n"), getprogname());
    printf (_("Search for PATTERN in each FILE or standard input.\n"));
    printf (_("PATTERN is, by default, a basic regular expression (BRE).\n"));
    printf (_("\
              Example: %s -i 'hello world' menu.h main.c\n\
              \n\
              Regexp selection and interpretation:\n"), getprogname());
    printf (_("\
              -E, --extended-regexp     PATTERN is an extended regular expression (ERE)\n\
              -F, --fixed-strings       PATTERN is a set of newline-separated strings\n\
              -G, --basic-regexp        PATTERN is a basic regular expression (BRE)\n\
              -P, --perl-regexp         PATTERN is a Perl regular expression\n"));
    /* -X is deliberately undocumented.  */
    printf (_("\
              -e, --regexp=PATTERN      use PATTERN for matching\n\
              -f, --file=FILE           obtain PATTERN from FILE\n\
              -i, --ignore-case         ignore case distinctions\n\
              -w, --word-regexp         force PATTERN to match only whole words\n\
              -x, --line-regexp         force PATTERN to match only whole lines\n\
              -z, --null-data           a data line ends in 0 byte, not newline\n"));
    printf (_("\
              \n\
              Miscellaneous:\n\
              -s, --no-messages         suppress error messages\n\
              -v, --invert-match        select non-matching lines\n\
              -V, --version             display version information and exit\n\
              --help                display this help text and exit\n"));
    printf (_("\
              \n\
              Output control:\n\
              -m, --max-count=NUM       stop after NUM matches\n\
              -b, --byte-offset         print the byte offset with output lines\n\
              -n, --line-number         print line number with output lines\n\
              --line-buffered       flush output on every line\n\
              -H, --with-filename       print the file name for each match\n\
              -h, --no-filename         suppress the file name prefix on output\n\
              --label=LABEL         use LABEL as the standard input file name prefix\n\
              "));
    printf (_("\
              -o, --only-matching       show only the part of a line matching PATTERN\n\
              -q, --quiet, --silent     suppress all normal output\n\
              --binary-files=TYPE   assume that binary files are TYPE;\n\
              TYPE is 'binary', 'text', or 'without-match'\n\
              -a, --text                equivalent to --binary-files=text\n\
              "));
    printf (_("\
              -I                        equivalent to --binary-files=without-match\n\
              -d, --directories=ACTION  how to handle directories;\n\
              ACTION is 'read', 'recurse', or 'skip'\n\
              -D, --devices=ACTION      how to handle devices, FIFOs and sockets;\n\
              ACTION is 'read' or 'skip'\n\
              -r, --recursive           like --directories=recurse\n\
              -R, --dereference-recursive  likewise, but follow all symlinks\n\
              "));
    printf (_("\
              --include=FILE_PATTERN  search only files that match FILE_PATTERN\n\
              --exclude=FILE_PATTERN  skip files and directories matching\
              FILE_PATTERN\n\
              --exclude-from=FILE   skip files matching any file pattern from FILE\n\
              --exclude-dir=PATTERN  directories that match PATTERN will be skipped.\n\
              "));
    printf (_("\
              -L, --files-without-match  print only names of FILEs containing no match\n\
              -l, --files-with-matches  print only names of FILEs containing matches\n\
              -c, --count               print only a count of matching lines per FILE\n\
              -T, --initial-tab         make tabs line up (if needed)\n\
              -Z, --null                print 0 byte after FILE name\n"));
    printf (_("\
              \n\
              Context control:\n\
              -B, --before-context=NUM  print NUM lines of leading context\n\
              -A, --after-context=NUM   print NUM lines of trailing context\n\
              -C, --context=NUM         print NUM lines of output context\n\
              "));
    printf (_("\
              -NUM                      same as --context=NUM\n\
              --color[=WHEN],\n\
              --colour[=WHEN]       use markers to highlight the matching strings;\n\
              WHEN is 'always', 'never', or 'auto'\n\
              -U, --binary              do not strip CR characters at EOL (MSDOS/Windows)\n\
              -u, --unix-byte-offsets   report offsets as if CRs were not there\n\
              (MSDOS/Windows)\n\
              \n"));
    printf (_("\
              'egrep' means 'grep -E'.  'fgrep' means 'grep -F'.\n\
              Direct invocation as either 'egrep' or 'fgrep' is deprecated.\n"));
    printf (_("\
              When FILE is -, read standard input.  With no FILE, read . if a command-line\n\
              -r is given, - otherwise.  If fewer than two FILEs are given, assume -h.\n\
              Exit status is 0 if any line is selected, 1 otherwise;\n\
              if any error occurs and -q is not given, the exit status is 2.\n"));
    emit_bug_reporting_address ();
  }
  exit (status);
}

/* Pattern compilers and matchers.  */

static void
Gcompile (char const *pattern, size_t size)
{
  GEAcompile (pattern, size, RE_SYNTAX_GREP);
}

static void
Ecompile (char const *pattern, size_t size)
{
  GEAcompile (pattern, size, RE_SYNTAX_EGREP);
}

static void
Acompile (char const *pattern, size_t size)
{
  GEAcompile (pattern, size, RE_SYNTAX_AWK);
}

static void
GAcompile (char const *pattern, size_t size)
{
  GEAcompile (pattern, size, RE_SYNTAX_GNU_AWK);
}

static void
PAcompile (char const *pattern, size_t size)
{
  GEAcompile (pattern, size, RE_SYNTAX_POSIX_AWK);
}

struct matcher
{
  char const name[16];
  compile_fp_t compile;
  execute_fp_t execute;
};
static struct matcher const matchers[] = {
  { "grep",      Gcompile, EGexecute },
  { "egrep",     Ecompile, EGexecute },
  { "fgrep",     Fcompile,  Fexecute },
  { "awk",       Acompile, EGexecute },
  { "gawk",     GAcompile, EGexecute },
  { "posixawk", PAcompile, EGexecute },
  { "perl",      Pcompile,  Pexecute },
  { "", NULL, NULL },
};
static reg_syntax_t syntax_bits;
static bool no_syntax_bits = false;
/* Set the matcher to M if available.  Exit in case of conflicts or if
 M is not available.  */
static void
setmatcher (char const *m)
{
  struct matcher const *p;
  
  if (matcher && !STREQ (matcher, m))
    error (EXIT_TROUBLE, 0, _("conflicting matchers specified"));
  
  for (p = matchers; p->compile; p++)
  {
    if (STREQ (m, p->name))
    {
      matcher = p->name;
      compile = p->compile;
      execute = p->execute;
      if (compile == Gcompile)
        syntax_bits = RE_SYNTAX_GREP;
      else if (compile == Ecompile)
        syntax_bits = RE_SYNTAX_EGREP;
      else if (compile == Acompile)
        syntax_bits = RE_SYNTAX_AWK;
      else if (compile == GAcompile)
        syntax_bits = RE_SYNTAX_GNU_AWK;
      else if (compile == PAcompile)
        syntax_bits = RE_SYNTAX_POSIX_AWK;
      else
        no_syntax_bits = true;
      return;
    }
  }
  error (EXIT_TROUBLE, 0, _("invalid matcher %s"), m);
}

/* Find the white-space-separated options specified by OPTIONS, and
 using BUF to store copies of these options, set ARGV[0], ARGV[1],
 etc. to the option copies.  Return the number N of options found.
 Do not set ARGV[N] to NULL.  If ARGV is NULL, do not store ARGV[0]
 etc.  Backslash can be used to escape whitespace (and backslashes).  */
static size_t
prepend_args (char const *options, char *buf, char **argv)
{
  char const *o = options;
  char *b = buf;
  size_t n = 0;
  
  for (;;)
  {
    while (c_isspace (to_uchar (*o)))
      o++;
    if (!*o)
      return n;
    if (argv)
      argv[n] = b;
    n++;
    
    do
      if ((*b++ = *o++) == '\\' && *o)
        b[-1] = *o++;
    while (*o && ! c_isspace (to_uchar (*o)));
    
    *b++ = '\0';
  }
}

/* Prepend the whitespace-separated options in OPTIONS to the argument
 vector of a main program with argument count *PARGC and argument
 vector *PARGV.  Return the number of options prepended.  */
static int
prepend_default_options (char const *options, int *pargc, char ***pargv)
{
  if (options && *options)
  {
    char *buf = xmalloc (strlen (options) + 1);
    size_t prepended = prepend_args (options, buf, NULL);
    int argc = *pargc;
    char *const *argv = *pargv;
    char **pp;
    enum { MAX_ARGS = MIN (INT_MAX, SIZE_MAX / sizeof *pp - 1) };
    if (MAX_ARGS - argc < prepended)
      xalloc_die ();
    pp = xmalloc ((prepended + argc + 1) * sizeof *pp);
    *pargc = prepended + argc;
    *pargv = pp;
    *pp++ = *argv++;
    pp += prepend_args (options, buf, pp);
    while ((*pp++ = *argv++))
      continue;
    return prepended;
  }
  
  return 0;
}

/* Get the next non-digit option from ARGC and ARGV.
 Return -1 if there are no more options.
 Process any digit options that were encountered on the way,
 and store the resulting integer into *DEFAULT_CONTEXT.  */
static int
get_nondigit_option (int argc, char *const *argv, intmax_t *default_context)
{
  static int prev_digit_optind = -1;
  int this_digit_optind;
  bool was_digit;
  char buf[INT_BUFSIZE_BOUND (intmax_t) + 4];
  char *p = buf;
  int opt;
  
  was_digit = false;
  this_digit_optind = optind;
  while (true)
  {
    opt = getopt_long (argc, (char **) argv, short_options,
                       long_options, NULL);
    if (! c_isdigit (opt))
      break;
    
    if (prev_digit_optind != this_digit_optind || !was_digit)
    {
      /* Reset to start another context length argument.  */
      p = buf;
    }
    else
    {
      /* Suppress trivial leading zeros, to avoid incorrect
       diagnostic on strings like 00000000000.  */
      p -= buf[0] == '0';
    }
    
    if (p == buf + sizeof buf - 4)
    {
      /* Too many digits.  Append "..." to make context_length_arg
       complain about "X...", where X contains the digits seen
       so far.  */
      strcpy (p, "...");
      p += 3;
      break;
    }
    *p++ = opt;
    
    was_digit = true;
    prev_digit_optind = this_digit_optind;
    this_digit_optind = optind;
  }
  if (p != buf)
  {
    *p = '\0';
    context_length_arg (buf, default_context);
  }
  
  return opt;
}

/* Parse GREP_COLORS.  The default would look like:
 GREP_COLORS='ms=01;31:mc=01;31:sl=:cx=:fn=35:ln=32:bn=32:se=36'
 with boolean capabilities (ne and rv) unset (i.e., omitted).
 No character escaping is needed or supported.  */
static void
parse_grep_colors (void)
{
  const char *p;
  char *q;
  char *name;
  char *val;
  
  p = getenv ("GREP_COLORS"); /* Plural! */
  if (p == NULL || *p == '\0')
    return;
  
  /* Work off a writable copy.  */
  q = xstrdup (p);
  
  name = q;
  val = NULL;
  /* From now on, be well-formed or you're gone.  */
  for (;;)
    if (*q == ':' || *q == '\0')
    {
      char c = *q;
      struct color_cap const *cap;
      
      *q++ = '\0'; /* Terminate name or val.  */
      /* Empty name without val (empty cap)
       * won't match and will be ignored.  */
      for (cap = color_dict; cap->name; cap++)
        if (STREQ (cap->name, name))
          break;
      /* If name unknown, go on for forward compatibility.  */
      if (cap->var && val)
        *(cap->var) = val;
      if (cap->fct)
        cap->fct ();
      if (c == '\0')
        return;
      name = q;
      val = NULL;
    }
    else if (*q == '=')
    {
      if (q == name || val)
        return;
      *q++ = '\0'; /* Terminate name.  */
      val = q; /* Can be the empty string.  */
    }
    else if (val == NULL)
      q++; /* Accumulate name.  */
    else if (*q == ';' || c_isdigit (*q))
      q++; /* Accumulate val.  Protect the terminal from being sent crap.  */
    else
      return;
}

/* Return true if PAT (of length PATLEN) contains an encoding error.  */
static bool
contains_encoding_error (char const *pat, size_t patlen)
{
  mbstate_t mbs = { 0 };
  size_t i, charlen;
  
  for (i = 0; i < patlen; i += charlen)
  {
    charlen = mb_clen (pat + i, patlen - i, &mbs);
    if ((size_t) -2 <= charlen)
      return true;
  }
  return false;
}

/* Return true if the fgrep pattern PAT, of size PATLEN, matches only
 single-byte characters including case folding, and so is suitable
 to be converted to a grep pattern.  */

static bool
fgrep_icase_available (char const *pat, size_t patlen)
{
  bool used[UCHAR_MAX + 1] = { 0, };
  
  for (size_t i = 0; i < patlen; i++)
  {
    unsigned char c = pat[i];
    if (localeinfo.sbctowc[c] == WEOF)
      return false;
    used[c] = true;
  }
  
  for (int c = 0; c <= UCHAR_MAX; c++)
    if (used[c])
    {
      wint_t wc = localeinfo.sbctowc[c];
      wchar_t folded[CASE_FOLDED_BUFSIZE];
      size_t nfolded = case_folded_counterparts (wc, folded);
      
      for (size_t i = 0; i < nfolded; i++)
      {
        char s[MB_LEN_MAX];
        mbstate_t mb_state = { 0 };
        if (1 < wcrtomb (s, folded[i], &mb_state))
          return false;
      }
    }
  
  return true;
}

/* Change the pattern *KEYS_P, of size *LEN_P, from fgrep to grep style.  */

static void
fgrep_to_grep_pattern (char **keys_p, size_t *len_p)
{
  size_t len = *len_p;
  char *keys = *keys_p;
  mbstate_t mb_state = { 0 };
  char *new_keys = xnmalloc (len + 1, 2);
  char *p = new_keys;
  size_t n;
  
  for (; len; keys += n, len -= n)
  {
    n = mb_clen (keys, len, &mb_state);
    switch (n)
    {
      case (size_t) -2:
        n = len;
        /* Fall through.  */
      default:
        p = mempcpy (p, keys, n);
        break;
        
      case (size_t) -1:
        memset (&mb_state, 0, sizeof mb_state);
        n = 1;
        /* Fall through.  */
      case 1:
        switch (*keys)
      {
        case '$': case '*': case '.': case '[': case '\\': case '^':
          *p++ = '\\'; break;
      }
        *p++ = *keys;
        break;
    }
  }
  
  free (*keys_p);
  *keys_p = new_keys;
  *len_p = p - new_keys;
}

int
main (int argc, char **argv)
{
  char *keys;
  size_t keycc, oldcc, keyalloc;
  bool with_filenames;
  size_t cc;
  int opt, prepended;
  int prev_optind, last_recursive;
  int fread_errno;
  intmax_t default_context;
  FILE *fp;
  exit_failure = EXIT_TROUBLE;
  initialize_main (&argc, &argv);
  
  keys = NULL;
  keycc = 0;
  with_filenames = false;
  eolbyte = '\n';
  filename_mask = ~0;
  
  max_count = INTMAX_MAX;
  
  /* The value -1 means to use DEFAULT_CONTEXT. */
  out_after = out_before = -1;
  /* Default before/after context: changed by -C/-NUM options */
  default_context = -1;
  /* Changed by -o option */
  only_matching = false;
  
  /* Internationalization. */
#if defined HAVE_SETLOCALE
  setlocale (LC_ALL, "");
#endif
#if defined ENABLE_NLS
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);
#endif
  
  init_localeinfo (&localeinfo);
  
  atexit (clean_up_stdout);
  
  last_recursive = 0;
  
  prepended = prepend_default_options (getenv ("GREP_OPTIONS"), &argc, &argv);
  if (prepended)
    error (0, 0, _("warning: GREP_OPTIONS is deprecated;"
                   " please use an alias or script"));
  
  compile = matchers[0].compile;
  execute = matchers[0].execute;
  
  bool exclude_include = false;
  while (prev_optind = optind,
         (opt = get_nondigit_option (argc, argv, &default_context)) != -1)
    switch (opt)
  {
    case 'A':
      context_length_arg (optarg, &out_after);
      break;
      
    case 'B':
      context_length_arg (optarg, &out_before);
      break;
      
    case 'C':
      /* Set output match context, but let any explicit leading or
       trailing amount specified with -A or -B stand. */
      context_length_arg (optarg, &default_context);
      break;
      
    case 'D':
      if (STREQ (optarg, "read"))
        devices = READ_DEVICES;
      else if (STREQ (optarg, "skip"))
        devices = SKIP_DEVICES;
      else
        error (EXIT_TROUBLE, 0, _("unknown devices method"));
      break;
      
    case 'E':
      setmatcher ("egrep");
      break;
      
    case 'F':
      setmatcher ("fgrep");
      break;
      
    case 'P':
      setmatcher ("perl");
      break;
      
    case 'G':
      setmatcher ("grep");
      break;
      
    case 'X': /* undocumented on purpose */
      setmatcher (optarg);
      break;
      
    case 'H':
      with_filenames = true;
      no_filenames = false;
      break;
      
    case 'I':
      binary_files = WITHOUT_MATCH_BINARY_FILES;
      break;
      
    case 'T':
      align_tabs = true;
      break;
      
    case 'U':
      dos_binary ();
      break;
      
    case 'u':
      dos_unix_byte_offsets ();
      break;
      
    case 'V':
      show_version = true;
      break;
      
    case 'a':
      binary_files = TEXT_BINARY_FILES;
      break;
      
    case 'b':
      out_byte = true;
      break;
      
    case 'c':
      count_matches = true;
      break;
      
    case 'd':
      directories = XARGMATCH ("--directories", optarg,
                               directories_args, directories_types);
      if (directories == RECURSE_DIRECTORIES)
        last_recursive = prev_optind;
      break;
      
    case 'e':
      cc = strlen (optarg);
      keys = xrealloc (keys, keycc + cc + 1);
      strcpy (&keys[keycc], optarg);
      keycc += cc;
      keys[keycc++] = '\n';
      fl_add (keys, keycc - cc - 1, keycc, "");
      break;
      
    case 'f':
      fp = STREQ (optarg, "-") ? stdin : fopen (optarg, O_TEXT ? "rt" : "r");
      if (!fp)
        error (EXIT_TROUBLE, errno, "%s", optarg);
      for (keyalloc = 1; keyalloc <= keycc + 1; keyalloc *= 2)
        ;
      keys = xrealloc (keys, keyalloc);
      oldcc = keycc;
      while ((cc = fread (keys + keycc, 1, keyalloc - 1 - keycc, fp)) != 0)
      {
        keycc += cc;
        if (keycc == keyalloc - 1)
          keys = x2nrealloc (keys, &keyalloc, sizeof *keys);
      }
      fread_errno = errno;
      if (ferror (fp))
        error (EXIT_TROUBLE, fread_errno, "%s", optarg);
      if (fp != stdin)
        fclose (fp);
      /* Append final newline if file ended in non-newline. */
      if (oldcc != keycc && keys[keycc - 1] != '\n')
        keys[keycc++] = '\n';
      fl_add (keys, oldcc, keycc, xstrdup (optarg));
      break;
      
    case 'h':
      with_filenames = false;
      no_filenames = true;
      break;
      
    case 'i':
    case 'y':			/* For old-timers . . . */
      match_icase = true;
      break;
      
    case 'L':
      /* Like -l, except list files that don't contain matches.
       Inspired by the same option in Hume's gre. */
      list_files = LISTFILES_NONMATCHING;
      break;
      
    case 'l':
      list_files = LISTFILES_MATCHING;
      break;
      
    case 'm':
      switch (xstrtoimax (optarg, 0, 10, &max_count, ""))
    {
      case LONGINT_OK:
      case LONGINT_OVERFLOW:
        break;
        
      default:
        error (EXIT_TROUBLE, 0, _("invalid max count"));
    }
      break;
      
    case 'n':
      out_line = true;
      break;
      
    case 'o':
      only_matching = true;
      break;
      
    case 'p':
    {
      parallel_explicitly_specified = parallel = true;
      int max_num_threads = sysconf (_SC_NPROCESSORS_ONLN) * 6;
      num_threads = (int) strtol (optarg, NULL, 10);
      if (num_threads > max_num_threads)
        num_threads = max_num_threads;
      max_allowed_num_nodes = 33554432 * num_threads - 8; /* 33554432 = 2^25 */
      if (num_threads < 1)
        error (EXIT_TROUBLE, 0, _("number of threads has to be positive"));
      break;
    }
      
    case 'q':
      exit_on_match = true;
      exit_failure = 0;
      break;
      
    case 'R':
      fts_options = basic_fts_options | FTS_LOGICAL;
      /* Fall through.  */
    case 'r':
      directories = RECURSE_DIRECTORIES;
      last_recursive = prev_optind;
      if (!parallel)
      {
        parallel = true;
        num_threads = sysconf (_SC_NPROCESSORS_ONLN);
        max_allowed_num_nodes = 33554432 * num_threads - 8; /*33554432 = 2^25*/
      }
      break;
      
    case 's':
      suppress_errors = true;
      break;
      
    case 'v':
      out_invert = true;
      break;
      
    case 'w':
      match_words = true;
      break;
      
    case 'x':
      match_lines = true;
      break;
      
    case 'Z':
      filename_mask = 0;
      break;
      
    case 'z':
      eolbyte = '\0';
      break;
      
    case BINARY_FILES_OPTION:
      if (STREQ (optarg, "binary"))
        binary_files = BINARY_BINARY_FILES;
      else if (STREQ (optarg, "text"))
        binary_files = TEXT_BINARY_FILES;
      else if (STREQ (optarg, "without-match"))
        binary_files = WITHOUT_MATCH_BINARY_FILES;
      else
        error (EXIT_TROUBLE, 0, _("unknown binary-files type"));
      break;
      
    case COLOR_OPTION:
      if (optarg)
      {
        if (!strcasecmp (optarg, "always") || !strcasecmp (optarg, "yes")
            || !strcasecmp (optarg, "force"))
          color_option = 1;
        else if (!strcasecmp (optarg, "never") || !strcasecmp (optarg, "no")
                 || !strcasecmp (optarg, "none"))
          color_option = 0;
        else if (!strcasecmp (optarg, "auto") || !strcasecmp (optarg, "tty")
                 || !strcasecmp (optarg, "if-tty"))
          color_option = 2;
        else
          show_help = 1;
      }
      else
        color_option = 2;
      break;
      
    case EXCLUDE_OPTION:
    case INCLUDE_OPTION:
      exclude_include = true;
      for (int cmd = 0; cmd < 2; cmd++)
      {
        if (!excluded_patterns[cmd])
          excluded_patterns[cmd] = new_exclude ();
        add_exclude (excluded_patterns[cmd], optarg,
                     ((opt == INCLUDE_OPTION ? EXCLUDE_INCLUDE : 0)
                      | exclude_options (cmd)));
      }
      break;
    case EXCLUDE_FROM_OPTION:
      exclude_include = true;
      for (int cmd = 0; cmd < 2; cmd++)
      {
        if (!excluded_patterns[cmd])
          excluded_patterns[cmd] = new_exclude ();
        if (add_exclude_file (add_exclude, excluded_patterns[cmd],
                              optarg, exclude_options (cmd), '\n')
            != 0)
          error (EXIT_TROUBLE, errno, "%s", optarg);
      }
      break;
      
    case EXCLUDE_DIRECTORY_OPTION:
      exclude_include = true;
      strip_trailing_slashes (optarg);
      for (int cmd = 0; cmd < 2; cmd++)
      {
        if (!excluded_directory_patterns[cmd])
          excluded_directory_patterns[cmd] = new_exclude ();
        add_exclude (excluded_directory_patterns[cmd], optarg,
                     exclude_options (cmd));
      }
      break;
      
    case GROUP_SEPARATOR_OPTION:
      group_separator = optarg;
      break;
      
    case LINE_BUFFERED_OPTION:
      line_buffered = true;
      break;
      
    case LABEL_OPTION:
      label = optarg;
      break;
      
    case 0:
      /* long options */
      break;
      
    default:
      usage (EXIT_TROUBLE);
      break;
      
  }
  
  if (parallel_explicitly_specified)
  {
    if (directories != RECURSE_DIRECTORIES)
      error (EXIT_TROUBLE, 0, _("multithreading has to be used with -r"));
    if (out_before >= 0 || out_after >= 0 || default_context >= 0)
    {
      /* for now we disable context as there could be an extra leading separator */
      error (EXIT_TROUBLE, 0, _("multithreading doesn't support outputting context"));
    }
    if (line_buffered)
      error (EXIT_TROUBLE, 0, _("multithreading doesn't support line buffering"));
    if (exclude_include)
      error (EXIT_TROUBLE, 0, _("multithreading doesn't support include/exclude options"));
    if (match_words)
      error (EXIT_TROUBLE, 0, _("multithreading doesn't support the match words options"));
  }
  else if (parallel)
  {
    if (match_words || exclude_include || line_buffered || out_before >= 0 || out_after >= 0 || default_context >= 0)
      parallel = false;
  }
  
  if (show_version)
  {
    version_etc (stdout, getprogname(), PACKAGE_NAME, VERSION, AUTHORS,
                 (char *) NULL);
    return EXIT_SUCCESS;
  }
  
  if (show_help)
    usage (EXIT_SUCCESS);
  
  bool possibly_tty = false;
  struct stat tmp_stat;
  if (! exit_on_match && fstat (STDOUT_FILENO, &tmp_stat) == 0)
  {
    if (S_ISREG (tmp_stat.st_mode))
      out_stat = tmp_stat;
    else if (S_ISCHR (tmp_stat.st_mode))
    {
      struct stat null_stat;
      if (stat ("/dev/null", &null_stat) == 0
          && SAME_INODE (tmp_stat, null_stat))
        exit_on_match = true;
      else
        possibly_tty = true;
    }
  }
  
  if (color_option == 2)
    color_option = possibly_tty && should_colorize () && isatty (STDOUT_FILENO);
  init_colorize ();
  
  if (color_option)
  {
    /* Legacy.  */
    char *userval = getenv ("GREP_COLOR");
    if (userval != NULL && *userval != '\0')
      selected_match_color = context_match_color = userval;
    
    /* New GREP_COLORS has priority.  */
    parse_grep_colors ();
  }
  
  /* POSIX says -c, -l and -q are mutually exclusive.  In this
   implementation, -q overrides -l and -L, which in turn override -c.  */
  if (exit_on_match)
    list_files = LISTFILES_NONE;
  if (exit_on_match || list_files != LISTFILES_NONE)
  {
    count_matches = false;
    done_on_match = true;
  }
  out_quiet = count_matches | done_on_match;
  
  if (out_after < 0)
    out_after = default_context;
  if (out_before < 0)
    out_before = default_context;
  
  if (keys)
  {
    if (keycc == 0)
    {
      /* No keys were specified (e.g. -f /dev/null).  Match nothing.  */
      out_invert ^= true;
      match_lines = match_words = false;
    }
    else
    /* Strip trailing newline. */
      --keycc;
  }
  else if (optind < argc)
  {
    /* A copy must be made in case of an xrealloc() or free() later.  */
    keycc = strlen (argv[optind]);
    keys = xmemdup (argv[optind++], keycc + 1);
    fl_add (keys, 0, keycc, "");
  }
  else
    usage (EXIT_TROUBLE);
  
  initialize_unibyte_mask ();
  
  /* In a unibyte locale, switch from fgrep to grep if
   the pattern matches words (where grep is typically faster).
   In a multibyte locale, switch from fgrep to grep if either
   (1) the pattern has an encoding error (where fgrep might not work), or
   (2) case is ignored and a fast fgrep ignore-case is not available.  */
  if (compile == Fcompile
      && (MB_CUR_MAX <= 1
          ? match_words
          : (contains_encoding_error (keys, keycc)
             || (match_icase && !fgrep_icase_available (keys, keycc)))))
  {
    fgrep_to_grep_pattern (&keys, &keycc);
    matcher = "grep";
    compile = Gcompile;
    execute = EGexecute;
  }
  if (parallel && !no_syntax_bits)
  {
    compile (keys, keycc);
    initialize_search_info_array (num_threads);
    for (int i = 0; i < num_threads; ++i)
    {
      GEAcompile_mthread (keys, keycc, syntax_bits,i);
    }
  }
  else
  {
    compile (keys, keycc);
  }
  free (keys);
  
  /* We need one byte prior and one after.  */
  char eolbytes[3] = { 0, eolbyte, 0 };
  size_t match_size;
  if (parallel && execute == EGexecute)
  {
    for (int i = 0; i < num_threads; ++i)
      skip_empty_lines = ((EGexecute_mthread (eolbytes + 1, 1, &match_size, NULL, i) == 0)
                          == out_invert);
  }
  else if (parallel)
  {
    for (int i = 0; i < num_threads; ++i)
      skip_empty_lines = ((execute (eolbytes + 1, 1, &match_size, NULL) == 0)
                          == out_invert);
  }
  else
  {
    skip_empty_lines = ((execute (eolbytes + 1, 1, &match_size, NULL) == 0)
                        == out_invert);
  }
  if ((argc - optind > 1 && !no_filenames) || with_filenames)
    out_file = 1;
  
#ifdef SET_BINARY
  /* Output is set to binary mode because we shouldn't convert
   NL to CR-LF pairs, especially when grepping binary files.  */
  if (!isatty (STDOUT_FILENO))
    SET_BINARY (STDOUT_FILENO);
#endif
  
  if (max_count == 0)
    return EXIT_FAILURE;
  
  /* Prefer sysconf for page size, as getpagesize typically returns int.  */
#ifdef _SC_PAGESIZE
  long psize = sysconf (_SC_PAGESIZE);
#else
  long psize = getpagesize ();
#endif
  if (! (0 < psize && psize <= (SIZE_MAX - sizeof (uword)) / 2))
    abort ();
  pagesize = psize;
  bufalloc = ALIGN_TO (INITIAL_BUFSIZE, pagesize) + pagesize + sizeof (uword);
  buffer = xmalloc (bufalloc);
  
  if (fts_options & FTS_LOGICAL && devices == READ_COMMAND_LINE_DEVICES)
    devices = READ_DEVICES;
  
  char *const *files;
  if (optind < argc)
  {
    files = argv + optind;
  }
  else if (directories == RECURSE_DIRECTORIES && prepended < last_recursive)
  {
    static char *const cwd_only[] = { (char *) ".", NULL };
    files = cwd_only;
    omit_dot_slash = true;
  }
  else
  {
    static char *const stdin_only[] = { (char *) "-", NULL };
    files = stdin_only;
  }
  
  bool status = true;
  do
    status &= grep_command_line_arg (*files++);
  while (*files != NULL);
  
  free_search_info_array ();
  
  /* We register via atexit() to test stdout.  */
  return errseen ? EXIT_TROUBLE : status;
}
