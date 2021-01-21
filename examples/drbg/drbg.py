#!/usr/bin/env python3
import os
import os.path
from saw import *
from saw.llvm import Contract
from saw.proofscript import yices
from cryptol import cry, cryptoltypes
#from saw.dashboard import Dashboard

dir_path = os.path.dirname(os.path.realpath(__file__))
conn = connect("cabal -v0 run exe:saw-remote-api socket")
view(DebugLog(err=None))
view(LogResults())
#view(Dashboard(path=__file__))

bcname = os.path.join(dir_path, '../all_llvm.bc')
cryname = '/home/dagit/local-data/saw/s2n/tests/saw/spec/DRBG/DRBG.cry'
drbghelpers = '/home/dagit/local-data/saw/saw-script/drbg-helpers.cry'

cryptol_load_file(cryname)
cryptol_load_file(drbghelpers)

mod = llvm_load_module(bcname)

def bytes_type(size):
    return llvm_types.array(size, llvm_types.i8)

blocksize = 16 # blocklen / 8
keysize = 16 # keylen / 8
seedsize = 32

blob_type = llvm_types.alias('struct.s2n_blob')
ctx_type = bytes_type(keysize)

def alloc_bytes(spec, n):
    return spec.alloc(bytes_type(n))

def alloc_blob(spec, n):
    p = spec.alloc(type=blob_type, read_only=True)
    datap = alloc_bytes(spec, n)
    spec.points_to(llvm.field(p, "data"), datap)
    spec.points_to(llvm.field(p, "size"), llvm.cryptol("`{n}:[32]".format(n=n)))
    spec.points_to(llvm.field(p, "allocated"), llvm.cryptol("0:[32]"))
    spec.points_to(llvm.field(p, "growable"), llvm.cryptol("0:[8]"))
    return (p, datap)

def alloc_blob_readonly(spec, n):
    p = spec.alloc(type=blob_type, read_only=True)
    datap = spec.alloc(llvm_types.array(n, llvm_types.i8), read_only = True)
    spec.points_to(llvm.field(p, "data"), datap)
    spec.points_to(llvm.field(p, "size"), llvm.cryptol("`{n}: [32]".format(n=n)))
    return(p, datap)

def alloc_init(spec, ty, v):
    p = spec.alloc(ty)
    spec.points_to(p,v)
    return p

def alloc_init_readonly(spec, ty, v):
    p = spec.alloc(ty, read_only = True)
    spec.points_to(p, v)
    return p

def ptr_to_fresh(spec, n, ty):
    x = spec.fresh_var(ty, n)
    p = alloc_init(spec, ty, x)
    return (x, p)

def fresh_ptr(spec, ty):
    x = spec.fresh_var(ty)
    p = spec.alloc(ty, points_to = x)
    return p

def ptr_to_fresh_readonly(spec, n, ty):
    x = spec.fresh_var(ty, n);
    p = alloc_init_readonly(spec, ty, x)
    return (x, p)

def drbg_state(spec, n):
    state = spec.alloc(llvm_types.alias("struct.s2n_drbg"))
    (key, keyp) = ptr_to_fresh(spec, "key", ctx_type)
    bytes_used = spec.fresh_var(llvm_types.i64, n+"bytes_used")
    mixes = spec.fresh_var(llvm_types.i64, n+"mixes")
    v = spec.fresh_var(bytes_type(blocksize), n+"v")
    spec.points_to(llvm.field(state, "bytes_used"), bytes_used)
    spec.points_to(llvm.field(state, "mixes"), mixes)
    spec.points_to(llvm.field(state, "ctx"), keyp)
    spec.points_to(llvm.field(state, "v"), v)
    return (state, keyp,
            "{{ bytes_used = {bytes_used}, ctx = {{ key = join {key} }}, v = join {v} }}".format(bytes_used=bytes_used.name(), key=key.name(), v=v.name()))
    #return (state, keyp,
    #        llvm.cryptol("{{ bytes_used = {bytes_used}, ctx = {{ key = join {key} }}, v = join {v} }}".format(bytes_used=bytes_used.name(), key=key.name(), v=v.name())))
    #return (state, keyp, { 'bytes_used': bytes_used , 'ctx': { 'key': llvm.cryptol("join {}".format(key.name())) } , v: llvm.cryptol("join {}".format(v)) })

    #       , {{ { bytes_used = bytes_used
    #           , ctx = { key = join key }
    #           , v = join v
    #           } }}

class blob_zero_spec(Contract):
    def __init__(self,n):
        super().__init__()
        self.n = n

    def specification(self):
        (p, datap) = alloc_blob(self, self.n)
        self.execute_func(p)
        self.points_to(datap, llvm.cryptol("zero:[{n}][8]".format(n=self.n)))
        self.returns(llvm.cryptol("0:[32]"))

class increment_drbg_counter_spec(Contract):
    def specification(self):
        (p, datap) = alloc_blob(self, blocksize)
        v = self.fresh_var(bytes_type(blocksize), "v")
        self.points_to(datap, v)
        self.execute_func(p)
        self.points_to(datap, llvm.cryptol("split ((join {v}) +1): [{blocksize}][8]".format(v=v.name(),blocksize=blocksize)))
        self.returns(llvm.cryptol("0:[32]"))

class bytes_used_spec(Contract):
    def specification(self):
        (sp, keyp, s) = drbg_state(self,"drbg")
        bytes_used = alloc_init(self, llvm_types.i64, llvm.cryptol("0:[64]"))
        self.execute_func(sp, bytes_used)
        self.points_to(bytes_used, llvm.cryptol("{s}.bytes_used".format(s=s)))
        self.returns(llvm.cryptol("0:[32]"))

class block_encrypt_spec(Contract):
    def specification(self):
        (key, keyp) = ptr_to_fresh_readonly(self, "ctx", ctx_type)
        (msg, msgp) = ptr_to_fresh_readonly(self, "msg", bytes_type(blocksize))
        outp = alloc_bytes(self, blocksize)
        self.execute_func(keyp, msgp, outp)
        self.points_to(outp, llvm.cryptol("encrypt_128 {key} {msg}".format(key=key.name(), msg=msg.name())))
        self.returns(llvm.cryptol("0 : [32]"))

class encryptUpdate_spec(Contract):
    def __init__(self,n):
        super().__init__()
        self.n = n
    def specification(self):
        # the first argument of `EVP_EncryptUpdate` is not `const`,
        # but it is constant in the DRBG cryptol specification.
        (key, keyp) = ptr_to_fresh_readonly(self, "key", ctx_type)
        outp = alloc_bytes(self, self.n)
        lenp = alloc_init(self, llvm_types.i32, llvm.cryptol("{} : [32]".format(self.n)))
        (msg, msgp) = ptr_to_fresh_readonly(self, "msg", (bytes_type(self.n)))
        self.execute_func(keyp, outp, lenp, msgp, llvm.cryptol("`{blocksize} : [32]".format(blocksize=blocksize)))
        self.points_to(outp, llvm.cryptol("encrypt_128 {} {}".format(key.name(), msg.name())))
        self.points_to(lenp, llvm.cryptol("{} : [32]".format(self.n)))
        self.returns (llvm.cryptol("1 : [32]"))

class bits_spec(Contract):
    def __init__(self, n):
        super().__init__()
        self.n = n
    def specification(self):
        (sp, keyp, s) = drbg_state(self, "drbg")
        (outp, datap) = alloc_blob(self, self.n)
        self.execute_func(sp, outp)
        res = "drbg_generate_internal `{{n={n}*8}} ({s})".format(n=self.n,s=s)
        # Remove some of the parens here to get really bad error messages
        c = llvm.cryptol("split (({res}).0) : [{n}][8]".format(res=res, n=self.n))
        self.points_to(datap, c)
        ensure_drbg_state(self, sp, keyp, "({res}).1".format(res=res))
        self.returns (llvm.cryptol(" 0 : [32] "))

def ensure_drbg_state(spec, p, keyp, s):
    spec.points_to(llvm.field(p, "bytes_used"), llvm.cryptol("({s}).bytes_used".format(s=s)))
    spec.points_to(llvm.field(p, "ctx"), keyp)
    spec.points_to(keyp, llvm.cryptol("split (({s}).ctx.key) : [{keysize}][8]".format(s=s,keysize=keysize)))
    spec.points_to(llvm.field(p, "v"), llvm.cryptol("split (({s}).v) : [{blocksize}][8]".format(s=s,blocksize=blocksize)))
    mixes = spec.fresh_var(llvm_types.i64, "mixes")
    spec.points_to(llvm.field(p, "mixes"), mixes)

#////////////////////////////////////////////////////////////////////////////////
#// Assumed specifications
#////////////////////////////////////////////////////////////////////////////////

class getenv_spec(Contract):
    def specification(self):
        p = self.alloc(llvm_types.i8)
        self.execute_func(p)
        self.returns(llvm.null)

class aes_128_ecb_spec(Contract):
    def specification(self):
        self.execute_func()
        r = self.alloc(ctx_type)
        self.returns(r)

class cipher_new_spec(Contract):
    def specification(self):
        self.execute_func()
        r = self.alloc(ctx_type)
        self.returns(r)

class cipher_init_spec(Contract):
    def specification(self):
        ctx = self.alloc(ctx_type)
        self.execute_func(ctx)
        key = self.fresh_var(ctx_type, "key")
        self.points_to(ctx, key)

class cipher_free_spec(Contract):
    def specification(self):
        ctx = self.alloc(ctx_type)
        self.execute_func(ctx)
        self.returns(llvm.void)

class cipher_cleanup_spec(Contract):
    def specification(self):
        ctx = self.alloc(ctx_type)
        self.execute_func(ctx)
        self.points_to(ctx, llvm.cryptol("zero : [{keysize}][8]".format(keysize=keysize)))
        self.returns(llvm.cryptol("1:[32]"))

class cipher_key_length_spec(Contract):
    def specification(self):
        ctx = self.alloc(ctx_type, read_only = True)
        self.execute_func(ctx)
        # Specialized to AES-128 for now
        self.returns(llvm.cryptol("16:[32]"))

class encryptInit_spec(Contract):
    def specification(self):
        ctx = self.alloc(ctx_type)
        #(ct, ctx) = ptr_to_fresh(self, "ctx", ctx_type)
        #(st, stp) = ptr_to_fresh(self, "st", ctx_type)
        #st = self.fresh_var(ctx_type)
        #stp = self.alloc(ctx_type, points_to = st)
        (key, keyp) = ptr_to_fresh_readonly(self, "key", ctx_type)
        #self.execute_func(ctx, stp, llvm.null, keyp, llvm.null)
        self.execute_func(ctx, llvm.null, llvm.null, keyp, llvm.null)
        self.points_to(ctx, key)
        self.returns(llvm.cryptol("1:[32]"))

class get_public_random_spec(Contract):
    def __init__(self):
        super().__init__()

    def specification(self):
        (p, datap) = alloc_blob(self, seedsize)
        self.execute_func(p)
        # TODO: blocked on 'fake_entropy'
        #self.points_to(datap, llvm.cryptol("split fake_entropy : [{seedsize}][8]".format(seedsize=seedsize)))
        self.returns(llvm.cryptol("0: [32]"))

class supports_rdrand_spec(Contract):
    def specification(self):
        self.execute_func()
        r = self.fresh_var(llvm_types.i8, "supports_rdrand")
        self.returns(r)

#////////////////////////////////////////////////////////////////////////////////
#// Assumptions about external functions
#////////////////////////////////////////////////////////////////////////////////

getenv_ov            = llvm_assume(mod, "getenv", getenv_spec())
aes_128_ecb_ov       = llvm_assume(mod, "EVP_aes_128_ecb", aes_128_ecb_spec())
cipher_new_ov        = llvm_assume(mod, "EVP_CIPHER_CTX_new", cipher_new_spec())
cipher_free_ov       = llvm_assume(mod, "EVP_CIPHER_CTX_free", cipher_free_spec())
#cipher_cleanup_ov    = llvm_assume(mod, "EVP_CIPHER_CTX_reset", cipher_cleanup_spec())
cipher_key_length_ov = llvm_assume(mod, "EVP_CIPHER_CTX_key_length", cipher_key_length_spec())
encryptInit_ov       = llvm_assume(mod, "EVP_EncryptInit_ex", encryptInit_spec())
#encryptInit_nokey_ov = llvm_assume(mod, "EVP_EncryptInit_ex", encryptInit_nokey_spec())
encryptUpdate_ov     = llvm_assume(mod, "EVP_EncryptUpdate", encryptUpdate_spec(16))
supports_rdrand_ov   = llvm_assume(mod, "s2n_cpu_supports_rdrand", supports_rdrand_spec())
# TODO: blocked on 'fake_entropy'
#get_public_random_ov = llvm_assume(mod, "s2n_get_public_random_data", get_public_random_spec())
get_seed_entropy_ov  = llvm_assume(mod, "s2n_get_seed_entropy", get_public_random_spec())
get_mix_entropy_ov   = llvm_assume(mod, "s2n_get_mix_entropy", get_public_random_spec())

###
class update_spec(Contract):
    def __init__(self, n):
        super().__init__()
        self.n = n
    def specification(self):
        (sp, keyp, s) = drbg_state(self, "drbg")
        (providedp, datap) = alloc_blob_readonly(self, self.n)
        data = self.fresh_var(bytes_type(self.n), "data")
        self.points_to(datap, data)
        self.execute_func(sp, providedp)
        ensure_drbg_state(self, sp, keyp, "drbg_update (join {data}) ({s})".format(data=data.name(), s=s))
        self.returns(llvm.cryptol("0:[32]"))

class seed_spec(Contract):
    def __init__(self, n):
        super().__init__()
        self.n = n
    def specification(self):
        (sp, keyp, s) = drbg_state(self, "drbg")
        (psp, datap) = alloc_blob_readonly(self, self.n)
        data = self.fresh_var(bytes_type(self.n), "data")
        self.points_to(datap, data)
        self.execute_func(sp, psp)
        expr = "drbg_reseed ({s}) (fake_entropy) (join ({data}))".format(s=s,
                data=data.name())
        ensure_drbg_state(self, sp, keyp, expr)
        self.returns(llvm.cryptol("0:[32]"))

zero_ov_block = llvm_verify(mod, 's2n_blob_zero', blob_zero_spec(blocksize))
zero_ov_seed = llvm_verify(mod, "s2n_blob_zero", blob_zero_spec(seedsize))
zero_ov_drbg = llvm_verify(mod, "s2n_blob_zero", blob_zero_spec(48))

inc_ov = llvm_verify(mod, "s2n_increment_drbg_counter", increment_drbg_counter_spec())
llvm_verify(mod, "s2n_drbg_bytes_used", bytes_used_spec())


blk_enc_ov = llvm_verify(mod, "s2n_drbg_block_encrypt", contract = block_encrypt_spec(), lemmas = [encryptUpdate_ov], script = yices(unints=['block_encrypt']))

bits_ov = llvm_verify(mod, "s2n_drbg_bits", contract = bits_spec(seedsize),
        lemmas = [inc_ov, encryptUpdate_ov, blk_enc_ov], script = yices(['block_encrypt']))

update_ov = llvm_verify(mod, "s2n_drbg_update", lemmas = [bits_ov,
    encryptInit_ov, aes_128_ecb_ov, cipher_key_length_ov], contract=
    update_spec(seedsize), script = yices(["block_encrypt"]))

# TODO: this lemma cannot be proven yet, see drbg-helpers.cry for the definition
# of "fake_entropy"
#seed_ov = llvm_verify(mod, "s3n_drbg_seed", lemmas = [get_public_random_ov,
#    get_seed_entropy_ov, update_ov, cipher_key_length_ov], contract =
#    seed_spec(seedsize),
#    script = yices(["block_encrypt"]))
