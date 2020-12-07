public class PropertiesTest {
    public static void main(String[] args)
        throws Exception {
        String value = System.getProperty("sun.boot.class.path");
        System.out.println(value);
    }
}
