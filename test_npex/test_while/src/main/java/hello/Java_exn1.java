package hello;
import java.io.InputStream;

class A {
  A f;
  int i;
  
  public int get_i() { return i; }
  public A get_f() { return this.f; }
}

public class Java_exn1 {
static boolean main(hello.A arg) {
    int n;
    int ret = 0;
    try {
      byte[] buffer = new byte[256];
      hello.A np = arg;/* np: non null pointer */

      while ((n = System.in.read(buffer)) != (-1)) {
          np = arg.get_f();/* np: null pointer */

          ret = ret + np.i;
      } 
      return ret == 0;
    }
    catch (Exception e) 
    {
      return false;
    }
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
