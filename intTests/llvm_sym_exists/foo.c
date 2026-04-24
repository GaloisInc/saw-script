int some_computation(int i);

int main_state = 13;

int foo(char inparr[], int idx) {
    if (some_computation(idx) > 10)
        return inparr[0] & main_state;
    else
        return inparr[idx];
}
