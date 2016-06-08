/**
 * The Simon family of block ciphers, described in
 * <em>The Simon and Speck Families of Lightweight Block Ciphers</em> by
 * <em>Ray Beaulieu, Douglas Shors, Jason Smith, Stefan Treatman-Clark, Bryan Weeks, Louis Wingers </em>
 * <p>
 * All block size and key size variants are supported, with the key size determined from the key
 * during {@link #init(boolean, CipherParameters)}.
 */
 
public class SimonEngine
{
    /** Simon32 - 16 bit words, 32 bit block size, 64 bit key */
    public static final int SIMON_32 = 32;

    /** Simon48 - 24 bit words, 48 bit block size, 72/96 bit key */
    public static final int SIMON_48 = 48;

    /** Simon64 - 32 bit words, 64 bit block size, 96/128 bit key */
    public static final int SIMON_64 = 64;

    /** Simon96 - 48 bit words, 96 bit block size, 96/144 bit key */
    public static final int SIMON_96 = 96;

    /** Simon128 - 64 bit words, 128 bit block size, 128/192/256 bit key */
    public static final int SIMON_128 = 128;

    private final SimonCipher cipher;
    
    public static void main(String[] args) {
      final byte[] key64 = {
        0x1b, 0x1a, 0x19, 0x18, 0x13, 0x12, 0x11, 0x10, 0x0b, 0x0a, 0x09, 0x08, 0x03, 0x02, 0x01, 0x00
      };
      final byte[] io64 = {
        0x65, 0x6b, 0x69, 0x6c, 0x20, 0x64, 0x6e, 0x75
      };
      encrypt(SIMON_64, key64, io64);
      printBytes(io64);
      decrypt(SIMON_64, key64, io64);
      printBytes(io64);
      
      final byte[] key128 = {
        0x1f, 0x1e, 0x1d, 0x1c, 0x1b, 0x1a, 0x19, 0x18, 0x17, 0x16, 0x15, 0x14, 0x13, 0x12, 0x11, 0x10, 
        0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00
      };
      final byte[] io128 = {
        0x74, 0x20, 0x6e, 0x69, 0x20, 0x6d, 0x6f, 0x6f, 0x6d, 0x69, 0x73, 0x20, 0x61, 0x20, 0x73, 0x69
      };
      encrypt(SIMON_128, key128, io128);
      printBytes(io128);
      decrypt(SIMON_128, key128, io128);
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
      SimonEngine se = new SimonEngine(blockSizeBits);
      se.init(forEncryption, key);
      se.processBlock(io, 0, io, 0);
    }

    /**
     * Constructs a Simon engine.
     *
     * @param blockSizeBits the block size (2 * the word size) in bits, one of {@link #SIMON_128},
     *            {@link #SIMON_96}, {@link #SIMON_64}, {@link #SIMON_48}, {@link #SIMON_32}.
     */
    public SimonEngine(final int blockSizeBits)
    {
        switch (blockSizeBits)
        {
        case SIMON_32:
            cipher = new Simon32Cipher();
            break;
        case SIMON_48:
            cipher = new Simon48Cipher();
            break;
        case SIMON_64:
            cipher = new Simon64Cipher();
            break;
        case SIMON_96:
            cipher = new Simon96Cipher();
            break;
        case SIMON_128:
            cipher = new Simon128Cipher();
            break;
        default:
            throw new IllegalArgumentException("Unknown Simon block size: " + blockSizeBits);
        }
    }

    /**
     * Initialises the Simon engine.
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
     * Gets the algorithm name of this Simon engine.
     *
     * @return the name of the Simon variant, specified to the level of the block size (e.g.
     *         <em>Simon96</em>).
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
     * Shared behaviour of Simon family block ciphers.
     */
    private static abstract class SimonCipher
    {
        /** Pre-computed z0...z4 round constants */
        private static final byte[][] Z = new byte[][] {
            {01, 01, 01, 01, 01, 00, 01, 00, 00, 00, 01, 00, 00, 01, 00, 01, 00, 01, 01, 00, 00, 00, 00, 01, 01, 01, 00, 00, 01, 01, 00, 01, 01, 01, 01, 01, 00, 01, 00, 00, 00, 01, 00, 00, 01, 00, 01, 00, 01, 01, 00, 00, 00, 00, 01, 01, 01, 00, 00, 01, 01, 00, },
            {01, 00, 00, 00, 01, 01, 01, 00, 01, 01, 01, 01, 01, 00, 00, 01, 00, 00, 01, 01, 00, 00, 00, 00, 01, 00, 01, 01, 00, 01, 00, 01, 00, 00, 00, 01, 01, 01, 00, 01, 01, 01, 01, 01, 00, 00, 01, 00, 00, 01, 01, 00, 00, 00, 00, 01, 00, 01, 01, 00, 01, 00, },
            {01, 00, 01, 00, 01, 01, 01, 01, 00, 01, 01, 01, 00, 00, 00, 00, 00, 00, 01, 01, 00, 01, 00, 00, 01, 00, 00, 01, 01, 00, 00, 00, 01, 00, 01, 00, 00, 00, 00, 01, 00, 00, 00, 01, 01, 01, 01, 01, 01, 00, 00, 01, 00, 01, 01, 00, 01, 01, 00, 00, 01, 01, },
            {01, 01, 00, 01, 01, 00, 01, 01, 01, 00, 01, 00, 01, 01, 00, 00, 00, 01, 01, 00, 00, 01, 00, 01, 01, 01, 01, 00, 00, 00, 00, 00, 00, 01, 00, 00, 01, 00, 00, 00, 01, 00, 01, 00, 00, 01, 01, 01, 00, 00, 01, 01, 00, 01, 00, 00, 00, 00, 01, 01, 01, 01, },
            {01, 01, 00, 01, 00, 00, 00, 01, 01, 01, 01, 00, 00, 01, 01, 00, 01, 00, 01, 01, 00, 01, 01, 00, 00, 00, 01, 00, 00, 00, 00, 00, 00, 01, 00, 01, 01, 01, 00, 00, 00, 00, 01, 01, 00, 00, 01, 00, 01, 00, 00, 01, 00, 00, 01, 01, 01, 00, 01, 01, 01, 01, }
        };

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
         * The index of the constant sequence to apply to a (possibly hypothetical) 2 word key.
         */
        private final int sequenceBase;

        /**
         * The actual number of rounds required for the initialised block size/key size.
         */
        protected int rounds;

        /**
         * Round constants for this instance, selected based on block size and key length.
         */
        protected byte[] constants;

        private boolean initialised = false;

        private boolean forEncryption;

        /**
         * Constructs a Simon cipher.
         *
         * @param wordSize the size of the word to use, in bytes.
         * @param sequenceBase the index of the constant sequence to apply to a (hypothetical) 2
         *            word key
         */
        protected SimonCipher(int wordSize, int sequenceBase)
        {
            this.wordSize = wordSize;
            this.sequenceBase = sequenceBase;
            this.blockSize = wordSize * 2;
            this.wordSizeBits = wordSize * 8;
        }

        public final String getAlgorithmName()
        {
            /*
             * Specify to block size level to be consistent with other variable key length algos
             * (e.g. AES) and to avoid / causing confusion in JCE publication.
             */
            return "Simon" + (blockSize * 8);
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

            rounds = checkKeySize(keyBytes.length);

            /*
             * Select constant sequence. Base sequence differs by family, but always increments per
             * key word.
             */
            final int keyWords = keyBytes.length / wordSize;
            this.constants = Z[sequenceBase + keyWords - 2];

            setKey(keyBytes);

            initialised = true;
        }

        /**
         * Checks whether a key size provided to the {@link #init(boolean, byte[])} method is valid,
         * and calculates the {@link SimonCipher#rounds} required based on the key length.
         *
         * @return the number of rounds to use for the key.
         */
        protected abstract int checkKeySize(int keySizeBytes);

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
         * NOTE: The Simon paper is not precise about the word and byte ordering, but the Simon team
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
     * Base class of Simon variants that fit in 32 bit Java integers: Simon32, Simon48, Simon64.
     * <p>
     * Simon32 and Simon48 (16 and 24 bit word sizes) are implemented using masking.
     */
    private static abstract class SimonIntCipher
        extends SimonCipher
    {
        /**
         * Pre-masked C
         */
        private final int c;

        /**
         * The expanded key schedule for all {@link SimonCipher#rounds}.
         */
        private int[] k;

        /**
         * The 2 words of the working state;
         */
        private int x, y;

        /**
         * Constructs a Simon cipher with <= 32 bit word size.
         *
         * @param wordSize the word size in bytes.
         * @param sequenceBase the sequence base to select the rounds constants with.
         */
        protected SimonIntCipher(int wordSize, int sequenceBase)
        {
            super(wordSize, sequenceBase);
            c = mask(0xfffffffc);
        }

        @Override
        protected void setKey(byte[] keyBytes)
        {
            k = new int[rounds];

            // Determine number of key words m
            int keyWords = keyBytes.length / wordSize;

            // Load k[m-1]..k[0]
            for (int i = 0; i < keyWords; i++)
            {
                k[i] = bytesToWord(keyBytes, (keyWords - i - 1) * wordSize);
            }

            // Key expansion
            for (int i = keyWords; i < rounds; i++)
            {
                int tmp = mask(rotr(k[i - 1], 3));
                if (keyWords == 4)
                {
                    tmp ^= k[i - 3];
                }
                tmp = mask(tmp ^ rotr(tmp, 1));
                k[i] = tmp ^ k[i - keyWords] ^ constants[(i - keyWords) % 62] ^ c;
            }
        }

        @Override
        protected void encryptBlock()
        {
            int x = this.x;
            int y = this.y;

            for (int r = 0; r < rounds; r++)
            {
                // Hotspot (at least) automatically unrolls loop and avoids tmp variable
                int tmp = x;
                x = mask(y ^ (rotl(x, 1) & rotl(x, 8)) ^ rotl(x, 2) ^ k[r]);
                y = tmp;
            }

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
                int tmp = y;
                y = mask(x ^ (rotl(y, 1) & rotl(y, 8)) ^ rotl(y, 2) ^ k[r]);
                x = tmp;
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
         * Read {@link SimonCipher#wordSize} bytes from the input data in big-endian order.
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
         * Writes {@link SimonCipher#wordSize} bytes into a buffer in big-endian order.
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
     * Base class of Simon variants that fit in 64 bit Java longs: Simon128, Simon96.
     * <p>
     * Simon96 (48 bit word size) is implemented using masking.
     */
    private static abstract class SimonLongCipher
        extends SimonCipher
    {
        /**
         * Pre-masked C
         */
        private final long c;

        /**
         * The expanded key schedule for all {@link SimonCipher#rounds}.
         */
        private long[] k;

        /**
         * The 2 words of the working state;
         */
        private long x, y;

        /**
         * Constructs a Simon cipher with <= 64 bit word size.
         *
         * @param wordSize the word size in bytes.
         * @param sequenceBase the sequence base to select the rounds constants with.
         */
        protected SimonLongCipher(int wordSize, int sequenceBase)
        {
            super(wordSize, sequenceBase);
            c = mask(0xfffffffffffffffcl);
        }

        @Override
        protected void setKey(byte[] keyBytes)
        {
            k = new long[rounds];

            // Determine number of key words m
            int keyWords = keyBytes.length / wordSize;

            // Load k[m-1]..k[0]
            for (int i = 0; i < keyWords; i++)
            {
                k[i] = bytesToWord(keyBytes, (keyWords - i - 1) * wordSize);
            }

            // Key expansion
            for (int i = keyWords; i < rounds; i++)
            {
                long tmp = mask(rotr(k[i - 1], 3));
                if (keyWords == 4)
                {
                    tmp ^= k[i - 3];
                }
                tmp = mask(tmp ^ rotr(tmp, 1));
                k[i] = tmp ^ k[i - keyWords] ^ constants[(i - keyWords) % 62] ^ c;
            }
        }

        @Override
        protected void encryptBlock()
        {
            long x = this.x;
            long y = this.y;

            for (int r = 0; r < rounds; r++)
            {
                // Hotspot (at least) automatically unrolls loop and avoids tmp variable
                long tmp = x;
                x = mask(y ^ (rotl(x, 1) & rotl(x, 8)) ^ rotl(x, 2) ^ k[r]);
                y = tmp;
            }

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
                long tmp = y;
                y = mask(x ^ (rotl(y, 1) & rotl(y, 8)) ^ rotl(y, 2) ^ k[r]);
                x = tmp;
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
         * Read {@link SimonCipher#wordSize} bytes from the input data in big-endian order.
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
         * Writes {@link SimonCipher#wordSize} bytes into a buffer in big-endian order.
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
     * Simon32: 2 byte words.
     * <p>
     * -2 sequence base (hypothetical)
     * <p>
     * 64 bit key/z0 sequence/32 rounds.
     */
    private static final class Simon32Cipher
        extends SimonIntCipher
    {

        protected Simon32Cipher()
        {
            super(2, -2);
        }

        @Override
        protected int mask(int val)
        {
            return (val & 0xffff);
        }

        @Override
        protected int checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 8)
            {
                throw new IllegalArgumentException("Simon32 requires a key of 64 bits.");
            }
            return 32;
        }

    }

    /**
     * Simon48: 3 byte words.
     * <p>
     * -1 sequence base
     * <p>
     * 72 bit key/z0 sequence/36 rounds.<br>
     * 96 bit key/z1 sequence/36 rounds.
     */
    private static final class Simon48Cipher
        extends SimonIntCipher
    {

        protected Simon48Cipher()
        {
            super(3, -1);
        }

        @Override
        protected int mask(int val)
        {
            return (val & 0xffffff);
        }

        @Override
        protected int checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 9 && keySizeBytes != 12)
            {
                throw new IllegalArgumentException("Simon48 requires a key of 72 or 96 bits.");
            }
            return 36;
        }

    }

    /**
     * Simon64: 4 byte words.
     * <p>
     * 1 sequence base (hypothetical)
     * <p>
     * 96 bit key/z2 sequence/42 rounds.<br>
     * 128 bit key/z3 sequence/44 rounds.
     */
    private static final class Simon64Cipher
        extends SimonIntCipher
    {

        protected Simon64Cipher()
        {
            super(4, 1);
        }

        @Override
        protected int mask(int val)
        {
            return val;
        }

        @Override
        protected int checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 12 && keySizeBytes != 16)
            {
                throw new IllegalArgumentException("Simon64 requires a key of 96 or 128 bits.");
            }
            return (keySizeBytes == 12) ? 42 : 44;
        }

    }

    /**
     * Simon96: 6 byte words.
     * <p>
     * 2 sequence base.
     * <p>
     * 96 bit key/z2 sequence/52 rounds.<br>
     * 144 bit key/z3 sequence/54 rounds.
     */
    private static final class Simon96Cipher
        extends SimonLongCipher
    {

        public Simon96Cipher()
        {
            super(6, 2);
        }

        @Override
        protected long mask(long val)
        {
            return (val & 0x0000ffffffffffffl);
        }

        @Override
        protected int checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 12 && keySizeBytes != 18)
            {
                throw new IllegalArgumentException("Simon96 requires a key of 96 or 144 bits.");
            }
            return (keySizeBytes == 12) ? 52 : 54;
        }
    }

    /**
     * Simon128: 8 byte words.
     * <p>
     * 2 sequence base.
     * <p>
     * 128 bit key/z2 sequence/68 rounds.<br>
     * 192 bit key/z3 sequence/69 rounds.<br>
     * 256 bit key/z4 sequence/72 rounds.
     */
    private static final class Simon128Cipher
        extends SimonLongCipher
    {

        public Simon128Cipher()
        {
            super(8, 2);
        }

        @Override
        protected long mask(long val)
        {
            return val;
        }

        @Override
        protected int checkKeySize(int keySizeBytes)
        {
            if (keySizeBytes != 16 && keySizeBytes != 24 && keySizeBytes != 32)
            {
                throw new IllegalArgumentException("Simon128 requires a key of 128, 192 or 256 bits.");
            }
            return (keySizeBytes == 16) ? 68 : ((keySizeBytes == 24) ? 69 : 72);
        }

    }

}
