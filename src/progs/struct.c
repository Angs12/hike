#include <stdio.h>
#include <stdlib.h>

typedef struct char_array {
  char *data;
  int len;
} char_array;

void print(int argc, char_array *a) {
  if (argc == 1) {
    puts("No arguments passed.\n");
    return;
  }
  puts(a->data);
}

int main(int argc, char *argv[]) {
  char_array *a = malloc(sizeof(char_array));
  a->data = malloc(sizeof(char) * 8);
  a->len = 8;
  a->data[0] = 'a';
  a->data[1] = 'b';
  a->data[2] = 'c';
  a->data[3] = 'd';
  a->data[4] = 'e';
  a->data[5] = 'f';
  a->data[6] = 'g';
  a->data[7] = '\0';
  puts("Calling print function.\n");
  print(argc, a);
  puts("Calling free function.\n");
  free(a->data);
  free(a);
  puts("This function doesn't need newline.\n");
}
