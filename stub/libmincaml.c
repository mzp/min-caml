#include <stdio.h>

void min_caml_print_newline(int unit) {
  putchar('\n');
}

void min_caml_print_int(int n) {
  printf("%d", n);
}

void min_caml_print_byte(char ch) {
  putchar(ch);
}

void min_caml_prerr_int(int n) {
  fprintf(stderr, "%d", n);
}

void min_caml_prerr_byte(char ch) {
  fputc(ch, stderr);
}

void min_caml_prerr_float(double f) {
  fprintf(stderr, "%lf", f);
}
