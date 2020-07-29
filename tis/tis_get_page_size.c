/* Find the page size using this and use it directly in 'src/libsodium/sodium/utils.c' */

#include <unistd.h>
#include <stdio.h>

int main(void){
  long sz = sysconf(_SC_PAGESIZE);
  printf("sysconf(_SC_PAGESIZE);== %ld\n", sz);
  return 0;
}
