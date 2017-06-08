int identity(int x) { return x; }
int example(void) { return identity(1) + identity(2); }
int bad_example(void) { return identity(3); }

unsigned int sum (unsigned int *arr, int n) {
        unsigned int acc = 0;
        for (int i = 0; i < n; i++) {
            acc += arr[i];
        }
        return acc;
}
unsigned int example_sums(void) {
        unsigned int nums[10] = {0,1,2,3,4,6,7,8,9};
        return sum(nums, 10) + sum(nums+2,6);
}

int myglobal;

void add_myglobal(int x) { myglobal = myglobal * myglobal; myglobal += x; }
int myglobal_example(void) {
  myglobal = 0;
  add_myglobal(10);
  add_myglobal(20);
  return myglobal;
}
