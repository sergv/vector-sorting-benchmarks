
#define SORT_NAME benchmarks
#define SORT_TYPE int

#include <sort.h>

void c_quicksort(int* xs, int len) {
    benchmarks_quick_sort(xs, len);
}

void c_heapsort(int* xs, int len) {
    benchmarks_heap_sort(xs, len);
}

void c_timsort(int* xs, int len) {
    benchmarks_tim_sort(xs, len);
}

void c_sqrtsort(int* xs, int len) {
    benchmarks_sqrt_sort(xs, len);
}

void c_grailsort(int* xs, int len) {
    benchmarks_grail_sort(xs, len);
}

void c_bitonicsort(int* xs, int len) {
    benchmarks_bitonic_sort(xs, len);
}
