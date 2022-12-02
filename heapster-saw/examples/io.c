#include<unistd.h>

#define HELLO "Hello, World!"

void hello_world () {
  write (1, HELLO, sizeof(HELLO));
}
