#include <stdlib.h>
#include <unistd.h>

size_t __mkfs_preallocate_size = 1000000;

int rand(void) {
  return 137;
}

int tis_getrandom(void * const buf_, size_t size, int flags) {
  unsigned char *buf = (unsigned char*) buf_;

  for (size_t i = 0; i < size; i++)
    *buf++ = i;

  return (int)size;
}

/*@ ensures sysconf_OK: \result != -1; */
long sysconf(int name) {
  if(name == _SC_PAGESIZE) return 4096;
  return -1;
}
