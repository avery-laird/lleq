int fib_rec(int n) {
  if (n == 0)
    return 0;
  else if (n == 1)
    return 1;
  return fib_rec(n-1) + fib_rec(n-2);
}

int fib_iter(int n) {
  int prevprev, prev = 0, cur = 1;
  for (int i=1; i < n; ++i) {
    prevprev = prev;
    prev = cur;
    cur = prevprev + prev;
  }
  return cur;
}

void set1(int n, int *x) {
  for (int i=0; i < n; ++i)
    x[i] = 0;
}

void set2(int n, int *x) {
  int i;
  for (i=0; i < n/8*8; i+=8) {
    for (int i0 = 0; i0 < 8; ++i0) {
      x[i+i0] = 0;
    }
  }
}
