//
// Created by avery on 17/09/22.
//

int tiled_loop(int *arr, int n) {
  int sum = 0;
  for (int i=0; i < n; ++i)
    sum += arr[i];
  return sum;
}

