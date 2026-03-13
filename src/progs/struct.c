#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct char_array {
  char *data;
  int len;
} char_array;

int main(int argc, char *argv[]) {
  char_array *a = malloc(sizeof(char_array));
  a->data = malloc(sizeof(char) * 8);
  a->len = 8;
  for (int i = 0; i < a->len; i++) {
    a->data[i] = 'a' + i;
  }
  for (int i = 0; i < a->len; i++) {
    putchar(a->data[i]);
  }
  putchar('\n');
  free(a->data);
  free(a);
}
