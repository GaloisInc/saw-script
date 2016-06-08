/**
 * The Speck family of block ciphers, described in
 * <em>The Simon and Speck Families of Lightweight Block Ciphers</em> by
 * <em>Ray Beaulieu, Douglas Shors, Jason Smith, Stefan Treatman-Clark, Bryan Weeks, Louis Wingers </em>
 * <p>
 * All block size and key size variants are supported, with the key size determined from the key
 * during {@link #init(boolean, CipherParameters)}.
 */
 
/* 
 From: https://github.com/timw/bc-java/tree/feature/simon-speck/core/src/main/java/org/bouncycastle/crypto/engines
 License: https://github.com/timw/bc-java/blob/feature/simon-speck/LICENSE.html
 
 Modifications:
 
 * Removed Bouncy Castle dependency
 
*/
public class SpeckEngine
{
    /** Speck32 - 16 bit words, 32 bit block size, 64 bit key */
    public static final int SPECK_32 = 32;

    /** Speck48 - 24 bit words, 48 bit block size, 72/96 bit key */
    public static final int SPECK_48 = 48;

    /** Speck64 - 32 bit words, 64 bit block size, 96/128 bit key */
    public static final int SPECK_64 = 64;

    /** Speck96 - 48 bit words, 96 bit block size, 96/144 bit key */
    public static final int SPECK_96 = 96;

    /** Speck128 - 64 bit words, 128 bit block size, 128/192/256 bit key */
    public static final int SPECK_128 = 128;

    private final SpeckCipher cipher;
    
    public static void main(String[] args) {
      final byte[] key64 = {
        0x1b, 0x1a, 0x19, 0x18, 0x13, 0x12, 0x11, 0x10, 0x0b, 0x0a, 0x09, 0x08, 0x03, 0x02, 0x01, 0x00
      };
      final byte[] io64 = {
        0x3b, 0x72, 0x65, 0x74, 0x74, 0x75, 0x43, 0x2d
      };
      encrypt(SPECK_64, key64, io64);
      printBytes(io64);
      decrypt(SPECK_64, key64, io64);
      printBytes(io64);
      
      final byte[] key128 = {
        0x1f, 0x1e, 0x1d, 0x1c, 0x1b, 0x1a, 0x19, 0x18, 0x17, 0x16, 0x15, 0x14, 0x13, 0x12, 0x11, 0x10,
        0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00
      };
      final byte[] io128 = {
        0x65, 0x73, 0x6f, 0x68, 0x74, 0x20, 0x6e, 0x49, 0x20, 0x2e, 0x72, 0x65, 0x6e, 0x6f, 0x6f, 0x70
      };
      encrypt(SPECK_128, key128, io128);
      printBytes(io128);
      decrypt(SPECK_128, key128, io128);
      printBytes(io128);
    }
    
    private static void printBytes(final byte[] data) {
      for (int i = 0; i < data.length; i++) {
        System.out.printf("%02X ", data[i]);
      }
      System.out.println();
    }
    
    public static void encrypt(final int blockSizeBits,
                               final byte[] key,
                               final byte[] io) {
      crypt(true, blockSizeBits, key, io);
    }
    
    public static void decrypt(final int blockSizeBits,
                               final byte[] key,
                               final byte[] io) {
      crypt(false, blockSizeBits, key, io);
    }
    
    private static void crypt(final boolean forEncryption,
                              final int blockSizeBits,
                              final byte[] key,
                              final byte[] io) {
      SpeckEngine se = new SpeckEngine(blockSizeBits);
      se.init(forEncryption, key);
      se.processBlock(io, 0, io, 0);
    }

    /**
     * Constructs a Speck engine.
     *
     * @param blockSizeBits the block size (2 * the word size) in bits, one of {@link #SPECK_128},
     *            {@link #SPECK_96}, {@link #SPECK_64}, {@link #SPECK_48}, {@link #SPECK_32}.
     */
    public SpeckEngine(final int blockSizeBits)
    {
        switch (blockSizeBits)
        {
        case SPECK_32:
            cipher = new Speck32Cipher();
            break;
        case SPECK_48:
            cipher = new Speck48Cipher();
            break;
        case SPECK_64:
            cipher = new Speck64Cipher();
            break;
        case SPECK_96:
            cipher = new Speck96Cipher();
            break;
        case SPECK_128:
            cipher = new Speck128Cipher();
            break;
        default:
            throw new IllegalArgumentException("Unknown Speck block size: " + blockSizeBits);
        }
    }

    /**
     * Initialises the Speck engine.
     *
     * @param a {@link KeyParameter} specifying a key with a length appropriate to the configured
     *            block size of this engine.
     */
    public void init(final boolean forEncryption, final byte[] keyBytes)
        throws IllegalArgumentException
    {
        cipher.init(forEncryption, keyBytes);
    }

    /**
     * Gets the algorithm name of this Speck engine.
     *
     * @return the name of the Speck variant, specified to the level of the block size (e.g.
     *         <em>Speck96</em>).
     */
    public String getAlgorithmName()
    {
        return cipher.getAlgorithmName();
    }

    public int getBlockSize()
    {
        return cipher.getBlockSize();
    }

    public int processBlock(final byte[] in, final int inOff, final byte[] out, final int outOff)
        throws IllegalArgumentException,
        IllegalStateException
    {
        cipher.processBlock(in, inOff, out, outOff);
        return cipher.getBlockSize();
    }

    public void reset()
    {
        cipher.reset();
    }

    /**
     * Shared behaviour of Speck family block ciphers.
     */
    private static abstract class SpeckCipher
    {
        /**
         * The block size of the cipher, in bytes.
         */
        protected final int blockSize;

        /**
         * The word size of the cipher, in bytes.
         */
        protected final int wordSize;

        /**
         * The word size of the cipher, in bits.
         */
        protected final int wordSizeBits;

        /**
         * The alpha round function rotation constant.
         */
        protected final int alpha;

        /**
         * The beta round function rotation constant.
         */
        protected final int beta;

        /**
         * The base number of rounds for a (potentially hypothetical) 2 word key variant of the
         * Speck cipher with this block size.
         */
        protected final int baseRounds;

        /**
         * The actual number of rounds required for the initialised block size/key size.
         */
        protected int rounds;

        private boolean initialised = false;

        private boolean forEncryption;

        /**
         * Constructs a Speck cipher.
         *
         * @param wordSize the size of the word to use, in bytes.
         * @param baseRounds the base number of rounds (for a 2 word key variant) for the specified
         *            word/block size.
         * @param alpha the alpha rotation constant to use.
         * @param beta the beta rotation constant to use.
         */
        protected SpeckCipher(int wordSize, int baseRounds, int alpha, int beta)
        {
            this.wordSize = wordSize;
            this.baseRounds = baseRounds;
            this.rounds = baseRounds;
            this.blockSize = wordSize * 2;
            this.wordSizeBits = wordSize * 8;
            this.alpha = alpha;
            this.beta = beta;
        }

        public final String getAlgorithmName()
        {
            /*
             * Specify to block size level to be consistent with other variable key length algos
             * (e.g. AES) and to avoid / causing confusion in JCE publication.
             */
            return "Speck" + (blockSize * 8);
        }

        public final int getBlockSize()
        {
            return blockSize;
        }

        /**
         * Initialise this cipher instance.
         *
         * @param forEncryption <code>true</code> for encryption, <code>false</code> for decryption.
         * @param keyBytes the bytes of the key to use.
         */
        public final void init(boolean forEncryption, byte[] keyBytes)
        {
            this.forEncryption = forEncryption;
            checkKeySize(keyBytes.length);
            setKey(keyBytes);
            initialised = true;
        }

        /**
         * Checks whether a key size provided to the {@link #init(boolean, byte[])} method is valid.
         */
        protected abstract void checkKeySize(int keySizeBytes);

        /**
         * Sets a key for this cipher instance, calculating the key schedule.
         */
        protected abstract void setKey(byte[] keyBytes);

        public final void processBlock(byte[] in, int inOff, byte[] out, int outOff)
        {
            if (!initialised)
            {
                throw new IllegalStateException(getAlgorithmName() + " engine not initialised");
            }

            if ((inOff + blockSize) > in.length)
            {
                throw new IllegalArgumentException("input buffer too short");
            }

            if ((outOff + blockSize) > out.length)
            {
                throw new IllegalArgumentException("output buffer too short");
            }

            unpackBlock(in, inOff);
            if (forEncryption)
            {
                encryptBlock();
            }
            else
            {
                decryptBlock();
            }
            packBlock(out, outOff);
        }

        /**
         * Unpack a block of data into working state prior to an encrypt/decrypt operation.
         *
         * @param in the input data.
         * @param inOff the offset to begin reading the input data at.
         */
        protected abstract void unpackBlock(byte[] in, int inOff);

        /*
         * NOTE: The Speck paper is not precise about the word and byte ordering, but the Speck team
         * have clarified in private correspondence that they prefer reverse word ordering in a byte
         * sequence and big endian byte ordering within words.
         *
         * e.g. a plaintext sequence of 2 words p0, p1, will be encoded in a byte array with p1
         * occurring prior (at lower indexes) to p0, and the bytes of p0 and p1 written in
         * big-endian (most significant byte first) order.
         *
         * This word/byte ordering is consistent with that used by (e.g.) Serpent.
         */

        /**
         * Packs the 2 word working state following an encrypt/decrypt into a byte sequence.
         *
         * @param out the output buffer.
         * @param outOff the offset to begin writing the output data at.
         */
        protected abstract void packBlock(byte[] out, int outOff);

        /**
         * Encrypts the plaintext words loaded with a previous call to
         * {@link #unpackBlock(byte[], int)}, leaving the resulting ciphertext words in the working
         * state.
         */
        protected abstract void encryptBlock();

        /**
         * Decrypts the ciphertext words loaded with a previous call to
         * {@link #unpackBlock(byte[], int)}, leaving the resulting plaintext words in the working
         * state.
         */
        protected abstract void decryptBlock();

        public void reset()
        {
        }
    }

    /**
     * Base class of Speck variants that fit in 32 bit Java integers: Speck32, Speck48, Speck64.
     * <p>
     * Speck32 and Speck48 (16 and 24 bit word sizes) are implemented using masking.
     */
    private static abstract class SpeckIntCipher
        extends SpeckCipher
    {
        /**
         * The expanded key schedule for all {@link SpeckCipher#rounds}.
         */
        private int[] k;

        /**
         * The 2 words of the working state;
         */
        private int x, y;

        /**
         * Constructs a Speck cipher with <= 32 bit word size, using the standard 8,3 rotation
         * constants.
         *
         * @param wordSize the word size in bytes.
         * @param baseRounds the base (for 2 word key) round count.
         */
        protected SpeckIntCipher(int wordSize, int baseRounds)
        {
            super(wordSize, baseRounds, 8, 3);
        }

        /**
         * Constructs a Speck cipher with <= 32 bit word size, using custom rotation constants.
         *
         * @param wordSize the word size in bytes.
         * @param baseRounds the base (for 2 word key) round count.
         * @param alpha the <em>alpha</em> rotation constant.
         * @param beta the <em>beta</em> rotation constant.
         */
        protected SpeckIntCipher(int wordSize, int baseRounds, int alpha, int beta)
        {
            super(wordSize, baseRounds, alpha, beta);
        }

        @Override
        protected void setKey(byte[] keyBytes)
        {
            // Determine number of key words m
            int keyWords = keyBytes.length / wordSize;

            // Number of rounds is increased by 1 for each key word > 2
            rounds = baseRounds + (keyWords - 2);
            k = new int[rounds];

            // Load k[0]
            k[0] = bytesToWord(keyBytes, (keyWords - 1) * wordSize);

            // Load l[m-2]...l[0], leave space for l[m-1] in key expansion
            final int[] l = new int[keyWords];
            for (int i = 0; i < keyWords - 1; i++)
            {
                l[i] = bytesToWord(keyBytes, (keyWords - i - 2) * wordSize);
            }

            // Key expansion using round function over l[m-2]...l[0],k[0] with round number as key
            for (int i = 0; i < rounds - 1; i++)
            {
                final int lw = (i + keyWords - 1) % keyWords;
                l[lw] = mask((rotr(l[i % keyWords], alpha) + k[i]) ^ i);
                k[i + 1] = mask(rotl(k[i], beta) ^ l[lw]);
            }
        }

        @Override
        protected void encryptBlock()
        {
            int x = this.x;
            int y = this.y;

            // System.out.printf("pt %08x,%08x\n", x, y);
            for (int r = 0; r < rounds; r++)
            {
                // System.out.printf("ct  %08x,%08x\n", x, y);
                // System.out.printf("ki  %08x\n", k[r]);
                // System.out.printf("r1  %08x\n", mask(rotr(x, alpha)));
                // System.out.printf("r2  %08x\n", mask(rotr(x, alpha) + y));
                // System.out.printf("r3  %08x\n", mask((rotr(x, alpha) + y) ^ k[r]));
                // System.out.printf("r4  %08x\n", mask(rotl(y, beta)));
                // System.out.printf("r5  %08x\n", mask(rotl(y, beta) ^ x));
                x = mask((rotr(x, alpha) + y) ^ k[r]);
                y = mask(rotl(y, beta) ^ x);
            }
            // System.out.printf("ctf %08x,%08x\n", x, y);
            // System.out.printf("etf 0000a868,000042f2\n");

            this.x = x;
            this.y = y;
        }

        @Override
        protected void decryptBlock()
        {
            int x = this.x;
            int y = this.y;

            for (int r = rounds - 1; r >= 0; r--)
            {
                y = mask(rotr(x ^ y, beta));
                x = mask(rotl(mask((x ^ k[r]) - y), alpha));
            }
            this.x = x;
            this.y = y;
        }

        /**
         * Masks all bits higher than the word size of this cipher in the supplied value.
         *
         * @param val the value to mask.
         * @return the masked value.
         */
        protected abstract int mask(int val);

        /**
         * Rotates a word left by the specified distance. <br>
         * The rotation is on the word size of the cipher instance, not on the full 64 bits of the
         * long.
         *
         * @param i the word to rotate.
         * @param distance the distance in bits to rotate.
         * @return the rotated word, which may have unmasked high (> word size) bits.
         */
        private int rotl(int i, int distance)
        {
            return ((i << distance) | (i >>> (wordSizeBits - distance)));
        }

        /**
         * Rotates a word right by the specified distance. <br>
         * The rotation is on the word size of the cipher instance, not on the full 64 bits of the
         * long.
         *
         * @param i the word to rotate.
         * @param distance the distance in bits to rotate.
         * @return the rotated word, which may have unmasked high (> word size) bits.
         */
        private int rotr(int i, int distance)
        {
            return ((i >>> distance) | (i << (wordSizeBits - distance)));
        }

        @Override
        protected void unpackBlock(byte[] in, int inOff)
        {
            // Reverse word order:
            // x,y == pt[1], pt[0]
            // == in[inOff..inOff + wordSize], in[in[inOff + wordSize..inOff + wordSize* 2]
            y = bytesToWord(in, inOff + wordSize);
            x = bytesToWord(in, inOff);
        }

        @Override
        protected void packBlock(byte[] out, int outOff)
        {
            wordToBytes(y, out, outOff + wordSize);
            wordToBytes(x, out, outOff);
        }

        /**
         * Read {@link SpeckCipher#wordSize} bytes from the input data in big-endian order.
         *
         * @param bytes the data to read a word from.
         * @param off the offset to read the word from.
         * @return the read word, with zeroes in any bits higher than the word size.
         */
        private int bytesToWord(final byte[] bytes, final int off)
        {
            if ((off + wordSize) > bytes.length)
            {
                throw new IllegalArgumentException();
            }

            int word = 0;
            int index = off;

            word = (bytes[index++] & 0xff);
            word = (word << 8) | (bytes[index++] & 0xff);
            if (wordSize > 2)
            {
                word = (word << 8) | (bytes[index++] & 0xff);
                if (wordSize > 3)
                {
                    word = (word << 8) | (bytes[index] & 0xff);
                }
            }

            return word;
        }

        /**
         * Writes {@link SpeckCipher#wordSize} bytes into a buffer in big-endian order.
         *
         * @param the word to write.
         * @param bytes the buffer to write the word bytes to.
         * @param off the offset to write the data at.
         */
        private void wordToBytes(final int word, final byte[] bytes, final int off)
        {
            if ((off + wordSize) > bytes.length)
            {
                throw new IllegalArgumentException();
            }

            int index = off + wordSize - 1;

            bytes[index--] = (byte)word;
            bytes[index--] = (byte)(word >> 8);
            if (wordSize > 2)
            {
                bytes[index--] = (byte)(word >> 16);
                if (wordSize > 3)
                {
                    bytes[index--] = (byte)(word >> 24);
                }
            }
        }
    }

    /**
     * Base class of Speck variants that fit in 64 bit Java longs: Speck128, Speck96.
     * <p>
     * Speck96 (48 bit word size) is implemented using masking.
     */
    private static abstract class SpeckLongCipher
        extends SpeckCipher
    {
        /**
         * The expanded key schedule for all {@link SpeckCipher#rounds}.
         */
        private long[] k;

        /**
         * The 2 words of the working state;
         */
        private long x, y;

        /**
         * Constructs a Speck cipher with <= 64 bit word size, using the standard 8,3 rotation
         * constants.
         *
         * @param wordSize the word size in bytes.
         * @param baseRounds the base (for 2 word key) round count.
         */
        protected SpeckLongCipher(int wordSize, int baseRounds)
        {
            super(wordSize, baseRounds, 8, 3);
        }

        @Override
        protected void setKey(byte[] keyBytes)
        {
            // Determine number of key words m
            int keyWords = keyBytes.length / wordSize;

            // Number of rounds is increased by 1 for each key word > 2
            rounds = baseRounds + (keyWords - 2);
            k = new long[rounds];

            // Load k[0]
            k[0] = bytesToWord(keyBytes, (keyWords - 1) * wordSize);

            // Load l[m-2]...l[0], leave space for l[m-1] in key expansion
            final long[] l = new long[keyWords];
            for (int i = 0; i < keyWords - 1; i++)
            {
                l[i] = bytesToWord(keyBytes, (keyWords - i - 2) * wordSize);
            }

            // Key expansion using round function over l[m-2]...l[0],k[0] with round number as key
            for (int i = 0; i < rounds - 1; i++)
            {
                final int lw = (i + keyWords - 1) % keyWords;
                l[lw] = mask((rotr(l[i % keyWords], alpha) + k[i]) ^ i);
                k[i + 1] = mask(rotl(k[i], beta) ^ l[lw]);
            }
        }

        @Override
        protected void encryptBlock()
        {
            long x = this.x;
            long y = this.y;

            // System.out.printf("pt %016x,%016x\n", x, y);
            for (int r = 0; r < rounds; r++)
            {
                // System.out.printf("ct  %016x,%016x\n", x, y);
                // System.out.printf("ki  %016x\n", k[r]);
                // System.out.printf("r1  %016x\n", rotr(x, alpha));
                // System.out.printf("r2  %016x\n", rotr(x, alpha) + y);
                // System.out.printf("r3  %016x\n", (rotr(x, alpha) + y) ^ k[r]);
                // System.out.printf("r4  %016x\n", rotl(y, beta));
                // System.out.printf("r5  %016x\n", rotl(y, beta) ^ x);
                x = mask((rotr(x, alpha) + y) ^ k[r]);
                y = mask(rotl(y, beta) ^ x);
            }
            // System.out.printf("ctf %016x,%016x\n", x, y);
            // System.out.printf("etf a65d985179783265,7860fedf5c570d18\n");

            this.x = x;
            this.y = y;
        }

        @Override
        protected void decryptBlock()
        {
            long x = this.x;
            long y = this.y;

            for (int r = rounds - 1; r >= 0; r--)
            {
                y = mask(rotr(x ^ y, beta));
                x = mask(rotl(mask((x ^ k[r]) - y), alpha));
            }
            this.x = x;
            this.y = y;
        }

        /**
         * Masks all bits higher than the word size of this cipher in the supplied value.
         *
         * @param val the value to mask.
         * @return the masked value.
         */
        protected abstract long mask(long val);

        /**
         * Rotates a word left by the specified distance. <br>
         * The rotation is on the word size of the cipher instance, not on the full 64 bits of the
         * long.
         *
         * @param i the word to rotate.
         * @param distance the distance in bits to rotate.
         * @return the rotated word, which may have unmasked high (> word size) bits.
         */
        private long rotl(long i, int distance)
        {
            return (i << distance) | (i >>> (wordSizeBits - distance));
        }

        /**
         * Rotates a word right by the specified distance. <br>
         * The rotation is on the word size of the cipher instance, not on the full 64 bits of the
         * long.
         *
         * @param i the word to rotate.
         * @param distance the distance in bits to rotate.
         * @return the rotated word, which may have unmasked high (> word size) bits.
         */
        private long rotr(long i, int distance)
        {
            return (i >>> distance) | (i << (wordSizeBits - distance));
        }

        @Override
        protected void unpackBlock(byte[] in, int inOff)
        {
            // Reverse word order:
            // x,y == pt[1], pt[0]
            // == in[inOff..inOff + wordSize], in[in[inOff + wordSize..inOff + wordSize* 2]
            y = bytesToWord(in, inOff + wordSize);
            x = bytesToWord(in, inOff);
        }

        @Override
        protected void packBlock(byte[] out, int outOff)
        {
            wordToBytes(y, out, outOff + wordSize);
            wordToBytes(x, out, outOff);
        }

        /**
         * Read {@link SpeckCipher#wordSize} bytes from the input data in big-endian order.
         *
         * @param bytes the data to read a word from.
         * @param off the offset to read the word from.
         * @return the read word, with zeroes in any bits higher than the word size.
         */
        private long bytesToWord(final byte[] bytes, final int off)
        {
            if ((off + wordSize) > bytes.length)
            {
                throw new IllegalArgumentException();
            }

            long word = 0;
            int index = off;

            word = (bytes[index++] & 0xffl);
            word = (word << 8) | (bytes[index++] & 0xffl);
            word = (word << 8) | (bytes[index++] & 0xffl);
            word = (word << 8) | (bytes[index++] & 0xffl);
            word = (word << 8) | (bytes[index++] & 0xffl);
            word = (word << 8) | (bytes[index++] & 0xffl);
            if (wordSize == 8)
            {
                word = (word << 8) | (bytes[index++] & 0xffl);
                word = (word << 8) | (bytes[index++] & 0xffl);
            }

            return word;
        }

        /**
         * Writes {@link SpeckCipher#wordSize} bytes into a buffer in big-endian order.
         *
         * @param the word to write.
         * @param bytes the buffer to write the word bytes to.
         * @param off the offset to write the data at.
         */
        private void wordToBytes(final long word, final byte[] bytes, final int off)
        {
            if ((off + wordSize) > bytes.length)
            {
                throw new IllegalArgumentException();
            }
            int index = off + wordSize - 1;

            bytes[index--] = (byte)word;
            bytes[index--] = (byte)(word >> 8);
            bytes[index--] = (byte)(word >> 16);
            bytes[index--] = (byte)(word >> 24);
            bytes[index--] = (byte)(word >> 32);
            bytes[index--] = (byte)(word >> 40);
            if (wordSize == 8)
            {
                bytes[index--] = (byte)(word >> 48);
                bytes[index--] = (byte)(word >> 56);
            }
        }

    }

    /**
     * Speck32: 2 byte words, 7/2 rotation constants.
     * <p>
     * 20 base rounds (hypothetical)
     * <p>
     * 64 bit key/22 rounds.
     */
    private static final class Speck32Cipher
        extends SpeckIntCipher
    {

        protected Speck32Cipher()
        {
            super(2, 20, 7, 2);
        }

        @Override
        protected int mask(int val)
        {
            return (val & 0xffff);
        }

        @Override
        protected void checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 8)
            {
                throw new IllegalArgumentException("Speck32 requires a key of 64 bits.");
            }
        }

    }

    /**
     * Speck48: 3 byte words, 8/3 rotation constants.
     * <p>
     * 21 base rounds (hypothetical)
     * <p>
     * 72 bit key/22 rounds.<br>
     * 96 bit key/23 rounds.
     */
    private static final class Speck48Cipher
        extends SpeckIntCipher
    {

        protected Speck48Cipher()
        {
            super(3, 21);
        }

        @Override
        protected int mask(int val)
        {
            return (val & 0xffffff);
        }

        @Override
        protected void checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 9 && keySizeBytes != 12)
            {
                throw new IllegalArgumentException("Speck48 requires a key of 72 or 96 bits.");
            }
        }

    }

    /**
     * Speck64: 4 byte words, 8/3 rotation constants.
     * <p>
     * 25 base rounds (hypothetical)
     * <p>
     * 96 bit key/26 rounds.<br>
     * 128 bit key/27 rounds.
     */
    private static final class Speck64Cipher
        extends SpeckIntCipher
    {

        protected Speck64Cipher()
        {
            super(4, 25);
        }

        @Override
        protected int mask(int val)
        {
            return val;
        }

        @Override
        protected void checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 12 && keySizeBytes != 16)
            {
                throw new IllegalArgumentException("Speck64 requires a key of 96 or 128 bits.");
            }
        }

    }

    /**
     * Speck96: 6 byte words, 8/3 rotation constants.
     * <p>
     * 28 base rounds
     * <p>
     * 96 bit key/28 rounds.<br>
     * 144 bit key/29 rounds.
     */
    private static final class Speck96Cipher
        extends SpeckLongCipher
    {

        public Speck96Cipher()
        {
            super(6, 28);
        }

        @Override
        protected long mask(long val)
        {
            return (val & 0x0000ffffffffffffl);
        }

        @Override
        protected void checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 12 && keySizeBytes != 18)
            {
                throw new IllegalArgumentException("Speck96 requires a key of 96 or 144 bits.");
            }
        }
    }

    /**
     * Speck128: 8 byte words, 8/3 rotation constants.
     * <p>
     * 32 base rounds
     * <p>
     * 128 bit key/32 rounds.<br>
     * 192 bit key/33 rounds.<br>
     * 256 bit key/34 rounds.
     */
    private static final class Speck128Cipher
        extends SpeckLongCipher
    {

        public Speck128Cipher()
        {
            super(8, 32);
        }

        @Override
        protected long mask(long val)
        {
            return val;
        }

        @Override
        protected void checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 16 && keySizeBytes != 24 && keySizeBytes != 32)
            {
                throw new IllegalArgumentException("Speck128 requires a key of 128, 192 or 256 bits.");
            }
        }

    }

}
