#include <stdio.h>

int main() {
  union {
    unsigned short value;
    unsigned char byte[2];
    struct {
      unsigned short one   : 1;
      unsigned short two   : 2;
      unsigned short three : 3;
      unsigned short four  : 4;
      unsigned short five  : 5;
    } field;
  } u;

  u.field.one   = 1;
  u.field.two   = 2;
  u.field.three = 3;
  u.field.four  = 4;
  u.field.five  = 5;

  printf("The fields are 1, 2, 3, 4, 5.\n");
  printf("The entire hex value is 0x%04x\n", u.value);
  printf("The first byte is 0x%02\n", u.byte[0]);
  printf("The second byte is 0x%02\n", u.byte[1]);

  return 0;
}
