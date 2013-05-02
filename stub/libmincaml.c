#include <stdio.h>
#include <math.h>

void min_caml_border() {
  puts("==========");
}
int dump(void* p){
  printf("[[%p]]\n", p);
  return 0;
}

void min_caml_debug(void* fv, int n) {
  printf("[%d]\n", n);
}
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

int min_caml_truncate(void* fv, double f) {
  return (int)f;
}

double min_caml_float_of_int(void* fv, int n){
  return (double)n;
}

double min_caml_cos(void* fv, double f) {
  return cos(f);
}
double min_caml_sin(void* fv, double f) {
  return sin(f);
}
double min_caml_tan(void* fv, double f) {
  return tan(f);
}
double min_caml_atan(void* fv, double f) {
  return atan(f);
}
