import org.bouncycastle.crypto.digests.*;
import com.galois.symbolic.*;

/**
   Writes out an AIG for the symbolic simulation of MD5 on an
   arbitrary 16-byte input message.
 */

class JavaMD5
{
    public static void main(String[] args) throws Exception
    {
        byte[] msg = Symbolic.freshByteArray(16);

	byte[] out = computeMD5( msg );

        Symbolic.writeAiger("JavaMD5.aig", out);
    }

    public static byte[] computeMD5( byte[] msg ) {
        byte[] out = new byte[16];
        MD5Digest digest = new MD5Digest();

        digest.update(msg, 0, msg.length);
        digest.doFinal(out, 0);

	return out;
    }
}
