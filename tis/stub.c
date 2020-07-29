
int rand(void) {
  return 137;
}

#ifdef __TIS_USER_OPEN

/* All the files in the tests are supposed to open correctly.
   In order to make sure that my filesystem configuration in the tis.config file
   is correct I wrap the 'open' function with an ACSL assertion. If there is any
   problem (i.e. if the return code is not 0), the Analyzer will report an
   Invalid Property and the test will be shown in red in TIS-CI. */

#include <stdarg.h>
#include <assert.h>

int __mkfs_open(const char * filename, int flags, va_list va);

/*@ ensures \result >= 0; */
int open(const char * filename, int flags, ...) {
  va_list va;
  va_start(va, flags);
  int rv = __mkfs_open(filename, flags, va);
  va_end(va);
  return rv;
}

#endif // __TIS_USER_OPEN
