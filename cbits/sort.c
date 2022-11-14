#include <stdint.h>

#define SORT_NAME benchmarks
#define SORT_TYPE int64_t

#include <sort.h>

void c_quicksort(int64_t* xs, int len) {
    benchmarks_quick_sort(xs, len);
}

void c_heapsort(int64_t* xs, int len) {
    benchmarks_heap_sort(xs, len);
}

void c_timsort(int64_t* xs, int len) {
    benchmarks_tim_sort(xs, len);
}

void c_sqrtsort(int64_t* xs, int len) {
    benchmarks_sqrt_sort(xs, len);
}

void c_grailsort(int64_t* xs, int len) {
    benchmarks_grail_sort(xs, len);
}

void c_bitonicsort(int64_t* xs, int len) {
    benchmarks_bitonic_sort(xs, len);
}
