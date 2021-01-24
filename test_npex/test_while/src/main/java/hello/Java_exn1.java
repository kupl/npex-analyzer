package hello;

class A {
  A f;

  public A get_f() {
    return this.f;
  }
}

public class Java_exn1 {
static boolean main(hello.A arg) {
    int n;
    int ret = 0;
    hello.A np = arg;/* np: non null pointer */

    while ((n = np.i) != (-1)) {
        np = arg.get_f();/* np: null pointer */

        ret = ret + np.i;
    } 
    return ret == 0;
}
  /* specification:
   * np == null -> n == -1 */

  public static boolean goo() {
    A p = new A();
    if (main(p) == false)
      return false;
    return true; 
  }
}
