#include <stdio.h>

void min_caml_print_newline(void* fv, int unit) {
  putchar('\n');
}

void min_caml_print_int(void* fv, int n) {
  printf("%d", n);
}

void min_caml_print_float(void* fv, double f) {
  printf("%lf", f);
}

void min_caml_print_byte(void* fv, char ch) {
  putchar(ch);
}

void min_caml_prerr_int(void* fv, int n) {
  fprintf(stderr, "%d", n);
}

void min_caml_prerr_byte(void* fv, char ch) {
  fputc(ch, stderr);
}

void min_caml_prerr_float(void* fv, double f) {
  fprintf(stderr, "%lf", f);
}
