#include <stdio.h>

int b;
extern int* const a;

int main() {
  b = 1;
  *a = 0;
  printf("%d\n", b + b);
  return 0;
}
