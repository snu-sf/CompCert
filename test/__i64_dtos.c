#include <stdio.h>

long long __i64_dtos(float t) {
  return 3;
}

int main() {
  printf("%lld\n", (long long) 5.0f); // expected: 5, actual: 3
  return 0;
}

