import java.io.FileNotFoundException;
import java.io.PrintStream;

class Foo {

    public static char[] value = { ' ', ' ', 'a' , ' ' };
    
}

class TestStr {
    public static String s = "Hello world";
    
    public static int main (int x) {

	s = "foo";
	return s.length();
    }

    public static int append (int x) {
	// String y = s + s;  // cannot translate string + , requires invokedynamic 
	return s.length();
    }


    // calling a string method
    public static int trim (int x) {
	String y = " A  ";
	return y.trim().length();
    }

    public static int pr (int x) throws FileNotFoundException {
	String y = "A";
	System.out.println(y); 
	return y.length();
    }

    
}
