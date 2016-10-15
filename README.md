git clone git://git.savannah.gnu.org/grep.git

replace bootstrap.conf with the bootstrap.conf here

cd grep/src/

Under src/ replace the original grep.c dosbuff.c dfasearch.c search.h Makefile.am with the corresponding five files here.

Then,

cd ..
./bootstrap
./configure
make

Multithreaded grep at the file granularity when used with the option -r or -R on directories.

Default number of threads is the number of cores online in the system.

To specify a custom number of threads use -p followed by the number of threads

Currently multithreading does not support context i.e. -A -B -C 
