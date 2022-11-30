#include<unistd.h>

#define HELLO "Hello, World!"

void hello_world () {
  write (2, HELLO, sizeof(HELLO));
}
