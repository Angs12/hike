#include <stdio.h>
#include <stdlib.h>

typedef struct char_array {
  char *data;
  int len;
} char_array;

int main(int argc, char *argv[]) {
  char_array *a = malloc(sizeof(char_array));
  a->data = malloc(sizeof(char) * 8);
  a->len = 8;
  // for (int i = 0; i < a->len; i++) {
  //   putchar(a->data[i]);
  // }
  putchar('\n');
  free(a->data);
  free(a);
  puts("This function doesn't need newline.\n");
}
