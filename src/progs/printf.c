#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
  char *s = malloc(10);
  sprintf(s, "Hello %s", "World!\n");
  printf(s);
}
