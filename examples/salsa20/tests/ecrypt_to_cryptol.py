#!/usr/bin/env python3
from enum import Enum
from math import log2

class ReadingState(Enum):
  (TYPE, SET, VECTOR) = range(3)

vector_names = []
vector_lists = {}

with \
    open("verified.test-vectors", 'r') as ECRYPT_TESTS_FILE, \
    open("Salsa20ECryptTests.cry", 'w') as CRYPTOL_TESTS_FILE, \
    open("Salsa20ECryptSubstreamTests.cry", 'w') as CRYPTOL_SUBSTREAM_TESTS_FILE:
  CRYPTOL_TESTS_FILE.write("""// Encryption examples based on ecrypt full verified test vectors at:
// http://www.ecrypt.eu.org/stream/svn/viewcvs.cgi/ecrypt/trunk/submissions/salsa20/full/verified.test-vectors?logsort=rev&rev=210&view=markup
module Salsa20ECryptTests where
  import Salsa20

  type Vector a w = {
    k : [16*a][8],
    v : [8][8],
    m : [w][8],
    e_c : [4][512],
    e_d : [512]
  }

  type Result = [5][64][8]

  /**
   * xor-digest function used for ecrypt test vectors
   */
  xor_digest : {w} (fin w) => [w * 64][8] -> [64][8]
  xor_digest c = foldl (^) zero (groupBy`{64} c)

  /**
   * Given a test vector, return results of encryption and digest, and whether results match expectations.
   */
  test :
    {
      s1, s2, a, w,
      w_64, w_s1, w_s2
    }
    (
      2 >= a, a >= 1, 70 >= (width w),
      2^^64 >= w_64,
      fin w_64, w == 64 * w_64, 64 * w_64 == 64 + (w_s1 + s1), 64 * w_64 == 64 + (w_s2 + s2)
    ) =>
    (Vector a w) -> (Result, Bit)
  test vector = (result, passes)
    where
      k = vector.k
      v = vector.v
      m = vector.m
      c = Salsa20_encrypt (k, v, m)
      [e_c0, e_c1, e_c2, e_c3] = vector.e_c
      e_d = vector.e_d

      r_c0 = take`{64} c
      r_c1 = take`{64, w_s1} (drop `{s1} c)
      r_c2 = take`{64, w_s2} (drop `{s2} c)
      r_c3 = drop`{back=64} c
      r_d = xor_digest`{w_64} c

      result = [r_c0, r_c1, r_c2, r_c3, r_d]
      passes = (map join result) == [e_c0, e_c1, e_c2, e_c3, e_d]

""")

  CRYPTOL_SUBSTREAM_TESTS_FILE.write("""// Encryption examples based on ecrypt full verified test vectors at:
// http://www.ecrypt.eu.org/stream/svn/viewcvs.cgi/ecrypt/trunk/submissions/salsa20/full/verified.test-vectors?logsort=rev&rev=210&view=markup
module Salsa20ECryptSubstreamTests where
  import Salsa20

  type Vector a w = {
    k : [16*a][8],
    v : [8][8],
    m : [64 * w][8],
    e_c : [4][512]
  }

  type Result = [4][64][8]

  /**
   * Encrypt a 64-byte substream of m starting at the given index s.
   */
  encryption' :
    {s, a, w, w_s}
    (
      2 >= a, a >= 1,
      64 >= (width s), w >= 1 + s, 64 + (64 * s) + w_s == 64 * w
    ) =>
    [16*a][8] -> [8][8] -> [64 * w][8] -> [64][8]
  encryption' k v m = c
    where
      seq' = Salsa20_expansion (k, v # (reverse (split (`s:[64]))))
      c = (take`{64, w_s} (drop`{64 * s} m)) ^ seq'

  /**
   * Property that just encrypting a substream has the same effect as taking
   * the same substream of the whole encrypted message (block independence).
   */
  encryption_substream_matches :
    {s, a, w, w_s, w'}
    (
      2 >= a, a >= 1,
      w >= 1 + s,
      64 >= (width s), 64 + (64 * s) + w_s == w',
      w' == 64 * w, 70 >= (width w'),
      2^^70 >= 64 + (64 * s + w_s),
      64 + (64 * s + w_s) == 64 * w  // Well duh.
    ) =>
    [16*a][8] -> [8][8] -> [w'][8] -> Bit
  encryption_substream_matches k v m =
    take`{64} (drop`{64 * s} (Salsa20_encrypt`{a, w'} (k, v, m))) == encryption'`{s, a, w, w_s} k v m

  // The substream encryption function matches the substreams of the original
  // for the small message sizes represented in most of the test vectors.
  property encryption_substream_matches_3_1_8 k v m = encryption_substream_matches`{3, 1, 8} k v m
  property encryption_substream_matches_4_1_8 k v m = encryption_substream_matches`{4, 1, 8} k v m
  property encryption_substream_matches_3_2_8 k v m = encryption_substream_matches`{3, 2, 8} k v m
  property encryption_substream_matches_4_2_8 k v m = encryption_substream_matches`{4, 2, 8} k v m

  // Corresponding properties for the larger ones are...a little harder to
  // prove via SAT solving.
  // property encryption_substream_matches_1023_1_2048 k v m = encryption_substream_matches`{1023, 1, 2048} k v m
  // property encryption_substream_matches_1024_1_2048 k v m = encryption_substream_matches`{1024, 1, 2048} k v m
  // property encryption_substream_matches_1023_2_2048 k v m = encryption_substream_matches`{1023, 2, 2048} k v m
  // property encryption_substream_matches_1024_2_2048 k v m = encryption_substream_matches`{1024, 2, 2048} k v m

  /**
   * Given a test vector, return results of substream encryption, and whether results match expectations.
   */
  test :
    {s1, s2, a, w, w_s1, w_s2, w_1}
    (
      2 >= a, a >= 1, s1 >= 1, s2 >= s1 + 1, w >= s2 + 1,
      64 >= width s1, 64 >= width s2, 64 >= width (w - 1),
      64 + (64 * s1 + w_s1) == 64 * w,
      64 + (64 * s2 + w_s2) == 64 * w,
      64 + (64 * (w - 1) + w_1) == 64 * w
    ) =>
    (Vector a w) -> (Result, Bit)
  test vector = (result, passes)
    where
      k = vector.k
      v = vector.v
      m = vector.m
      [e_c0, e_c1, e_c2, e_c3] = vector.e_c

      r_c0 = encryption'`{0} k v m
      r_c1 = encryption'`{s1, a, w, w_s1} k v m
      r_c2 = encryption'`{s2, a, w, w_s2} k v m
      r_c3 = encryption'`{w - 1, a, w, w_1} k v m

      result = [r_c0, r_c1, r_c2, r_c3]
      passes = (map join result) == [e_c0, e_c1, e_c2, e_c3]

""")

  # Encryption examples based on ecrypt full verified test vectors at:
  # http://www.ecrypt.eu.org/stream/svn/viewcvs.cgi/ecrypt/trunk/submissions/salsa20/full/verified.test-vectors?logsort=rev&rev=210&view=markup
  # (31 Aug 2017)
  # (Removed incorrect/extraneous "(stream is generated by encrypting
  # 512 zero bytes)" lines.)

  ECRYPT_TESTS_FILE.readline()  # ********************************************************************************
  ECRYPT_TESTS_FILE.readline()  # *              ECRYPT Stream Cipher Project            *
  ECRYPT_TESTS_FILE.readline()  # ********************************************************************************
  ECRYPT_TESTS_FILE.readline()  #
  ECRYPT_TESTS_FILE.readline()  # Primitive Name: Salsa20

  state = ReadingState.TYPE

  while True:
    if state == ReadingState.TYPE:
      ECRYPT_TESTS_FILE.readline()  # =======================
      ECRYPT_TESTS_FILE.readline()  # Profile: S3___
      line = ECRYPT_TESTS_FILE.readline()  # Key size: {128|256} bits

      if line.strip() == "":
        break

      k_bytelength = int(line[9:13]) >> 3

      ECRYPT_TESTS_FILE.readline()  # IV size: 64 bits
      ECRYPT_TESTS_FILE.readline()  #

      line = ECRYPT_TESTS_FILE.readline()  # Test vectors -- set 1

      state = ReadingState.SET
    elif state == ReadingState.SET:
      set_number = int(line[-2:-1])

      ECRYPT_TESTS_FILE.readline()  # =====================
      ECRYPT_TESTS_FILE.readline()  #

      line = ECRYPT_TESTS_FILE.readline()  # Set {\d}, vector#{\d+{1:3}}:

      state = ReadingState.VECTOR
    elif state == ReadingState.VECTOR:
      v_set_number = line[4:5]
      v_number = line[14:17].strip()

      line = ECRYPT_TESTS_FILE.readline()  #              key = {\d+}
      k = line[31:-1]

      line = ECRYPT_TESTS_FILE.readline()

      if line[29] == ' ':  #                {\d+}
        k += line[31:-1]
        line = ECRYPT_TESTS_FILE.readline()

      v = line[31:-1]  #               IV = {\d{16}}

      stream_data = []

      for i in range(4):
        line = ECRYPT_TESTS_FILE.readline()  #        stream[{\d+}..{\d+}] = 4DFA5E481DA23EA09A31022050859936
        (stream_indices_i, stream_value_i) = map(str.strip, line.split('='))
        (stream_start_i, stream_end_i) = map(int, stream_indices_i[7:-1].split(".."))
        line = ECRYPT_TESTS_FILE.readline()  #                DA52FCEE218005164F267CB65F5CFD7F
        stream_value_i += line[31:-1]
        line = ECRYPT_TESTS_FILE.readline()  #                2B4F97E0FF16924A52DF269515110A07
        stream_value_i += line[31:-1]
        line = ECRYPT_TESTS_FILE.readline()  #                F9E460BC65EF95DA58F740B7D1DBB0AA
        stream_value_i += line[31:-1]

        if (stream_end_i - stream_start_i != 63):
          throw(RuntimeError("Non-64!"))

        stream_data.append((stream_start_i, stream_end_i, stream_value_i))

      line = ECRYPT_TESTS_FILE.readline()  #           xor-digest = F7A274D268316790A67EC058F45C0F2A
      xor_digest = line[31:-1]
      line = ECRYPT_TESTS_FILE.readline()  #                067A99FCDE6236C0CEF8E056349FE54C
      xor_digest += line[31:-1]
      line = ECRYPT_TESTS_FILE.readline()  #                5F13AC74D2539570FD34FEAB06C57205
      xor_digest += line[31:-1]
      line = ECRYPT_TESTS_FILE.readline()  #                3949B59585742181A5A760223AFA22D4
      xor_digest += line[31:-1]
      line = ECRYPT_TESTS_FILE.readline()  #

      vector_name = "vector_{}_{}_{}".format(k_bytelength, v_set_number, v_number)
      vector_names.append(vector_name)

      CRYPTOL_TESTS_FILE.write("""  type {}_s1 = {}
  type {}_s2 = {}
  {} = {{
    k = groupBy`{{8}} 0x{},
    v = groupBy`{{8}} 0x{},
    m = zero:[{}][8],
    e_c = [
      0x{},
      0x{},
      0x{},
      0x{}
    ],
    e_d = 0x{}
  }}

""".format(
        vector_name, stream_data[1][0],
        vector_name, stream_data[2][0],
        vector_name,
        k,
        v,
        stream_data[3][1] + 1,
        stream_data[0][2], stream_data[1][2], stream_data[2][2], stream_data[3][2],
        xor_digest,
      ))

      CRYPTOL_SUBSTREAM_TESTS_FILE.write("""  type {}_s1 = {}
  type {}_s2 = {}
  {} = {{
    k = groupBy`{{8}} 0x{},
    v = groupBy`{{8}} 0x{},
    m = zero:[{}][8],
    e_c = [
      0x{},
      0x{},
      0x{},
      0x{}
    ]
  }}

""".format(
        vector_name, stream_data[1][0] >> 6,
        vector_name, stream_data[2][0] >> 6,
        vector_name,
        k,
        v,
        stream_data[3][1] + 1,
        stream_data[0][2], stream_data[1][2], stream_data[2][2], stream_data[3][2],
      ))

      line = ECRYPT_TESTS_FILE.readline()

      if line.startswith('S'):
        state = ReadingState.VECTOR  # Set {\d}, vector#{\d+{1:3}}:
      elif line.startswith('T'):
        state = ReadingState.SET
      elif line.strip() == "":
        vector_list_name = "tests_{}".format(k_bytelength)
        vector_lists[vector_list_name] = vector_names
        vector_names = []

        ECRYPT_TESTS_FILE.readline()  #
        ECRYPT_TESTS_FILE.readline()  # End of test vectors
        ECRYPT_TESTS_FILE.readline()  #
        ECRYPT_TESTS_FILE.readline()  # Primitive Name: Salsa20
        state = ReadingState.TYPE

  for (vector_list_name, vector_names) in vector_lists.items():
    for vector_name in vector_names:
      vector_test_and_property = """  {0}_test = test`{{{0}_s1, {0}_s2}} {0}
  property {0}_test_passes = {0}_test.1

""".format(vector_name)
      CRYPTOL_TESTS_FILE.write(vector_test_and_property)
      CRYPTOL_SUBSTREAM_TESTS_FILE.write(vector_test_and_property)

    property_vectors_pass = """
  /* property {}_pass = and [
    {}
  ] */

""".format(vector_list_name, ",\n    ".join(vector_name + "_test_passes" for vector_name in vector_names))

    CRYPTOL_TESTS_FILE.write(property_vectors_pass)
    CRYPTOL_SUBSTREAM_TESTS_FILE.write(property_vectors_pass)
