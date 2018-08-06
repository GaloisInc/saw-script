import java.io.FileNotFoundException;
import java.io.PrintStream;

class Foo {

    public static char[] value = { ' ', ' ', 'a' , ' ' };
    
    // testing constructing a new string, then returning from a method
    public String h () {
	int len = value.length;
        int st = 0;
        char[] val = value;    /* avoid getfield opcode */

        while ((st < len) && (val[st] <= ' ')) {
            st++;
        }
        while ((st < len) && (val[len - 1] <= ' ')) {
            len--;
        }
        return ((st > 0) || (len < value.length)) ? "a" : "bc" ;
    }

}

class TestStr {
    public static String s = "Hello world";
    
    public static int main (int x) {

	//	System.out.println(s);
	s = "foo";
	return s.length();
    }

    public static int append (int x) {
	// String y = s + s;  // cannot translate string + , requires invokedynamic 
	return s.length();
    }


    public static int test(int x) {
	String y = s.substring(0,2);
	return y.length();
    }
    
    // calling a string method
    public static int trim (int x) {
	String y = " A  ";
	return y.trim().length();
    }

    public static int pr (int x) throws FileNotFoundException {
	String y = "A";
	//System.out.println(y);  // null dereference, System.out is not initialized
	return y.length();
    }

    
}
