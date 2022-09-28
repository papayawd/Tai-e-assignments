class Assign {

    void assign() {
        int x = 1, y;
        x = 2;
        x = 3;
        x = 4;
        y = x;
    }

    void test(int x) {
        int a = 1, b = 2;
        if (x > 0) {
            a = 2;
            b = 1;
        }
        int c = a + b;

    }
}
