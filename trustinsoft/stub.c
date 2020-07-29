#include <stdlib.h>

// TIS CI creates a virtual filesystem that includes all test vectors (see trustinsoft/common.config). 
// For libsodium, its maximum size was too small. Hence, this limit had to be increased.
size_t __mkfs_preallocate_size = 1000000;

// TIS CI requires all the test cases to be deterministic, hence the rand() function has been stubbed
int rand(void) {
  return 137;
}

// tis_getrandom() replaces the getrandom() function (see trustinsoft/gcc_x86_64.config).
int tis_getrandom(void * const buf_, size_t size, int flags)
{ 
  unsigned char *buf = (unsigned char*) buf_;
  
  for (size_t i = 0; i < size; i++)
    *buf++ = i;

  return (int)size;
}
