#include <stdio.h>

long long runtime_read() {
  long long value = 0;
  scanf("%lld", &value);
  return value;
}

void runtime_write(long long value) {
  printf("%lld\n", value);
}
