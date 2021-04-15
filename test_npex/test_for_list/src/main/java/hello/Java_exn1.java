package hello;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;


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
    List<String> str_list = new ArrayList<String>();
    for (String str : str_list) {
      return true;
    }
    return true;
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
