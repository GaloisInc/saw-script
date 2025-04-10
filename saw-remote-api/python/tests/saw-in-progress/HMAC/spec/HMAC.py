import os
import os.path
from cryptol.cryptoltypes import to_cryptol
from saw_client import *
from saw_client.llvm import *
from env_server import *

# N.B., transliteration from HMAC.saw

dir_path = os.path.dirname(os.path.realpath(__file__))
c = env_connect()

# import "HMAC_iterative.cry";
cryptol_load_file(os.path.join(dir_path, 'HMAC_iterative.cry'))
# import "Hashing.cry";
cryptol_load_file(os.path.join(dir_path, 'Hashing.cry'))

################################
# Generic Utilities.

# let ptr_to_fresh n ty = do {
#     x <- crucible_fresh_var n ty;
#     p <- alloc_init ty (crucible_term x);
#     return (x, p);
# };
def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None, *, read_only : bool = False) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.
    
    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to=var, read_only=read_only)
    return (var, ptr)

# TODO(AMK) Um... what is this:
# let z3_hash_unint =
#     w4_unint_z3 [ "hash_init_c_state"
#                 , "hash_update_c_state"
#                 , "hash_update_c_state_unbounded"
#                 , "hash_digest_c_state"
#                 ];

# ////////////////////////////////////////////////////////////////
# // Hash.
# //

# let setup_hash_state pstate = do {
#     alg0 <- crucible_fresh_var "alg" (llvm_int 32);
#     h0 <- crucible_fresh_var "h" (llvm_array 8 (llvm_int 64));
#     Nl0 <- crucible_fresh_var "Nl" (llvm_int 64);
#     Nh0 <- crucible_fresh_var "Nh" (llvm_int 64);
#     u0 <- crucible_fresh_var "u" (llvm_array 16 (llvm_int 64));
#     num0 <- crucible_fresh_var "num" (llvm_int 32);
#     is_ready_for_input0 <- crucible_fresh_var "is_ready_for_input" (llvm_int 8);
#     currently_in_hash0 <- crucible_fresh_var "currently_in_hash" (llvm_int 64);
#     md_len0 <- crucible_fresh_var "md_len" (llvm_int 32);
#     (_, pimpl) <- ptr_to_fresh_readonly "impl" (llvm_alias "struct.s2n_hash");
#     crucible_points_to pstate
#       (crucible_struct
#         [ pimpl
#         , crucible_term alg0
#         , crucible_term is_ready_for_input0
#         , crucible_term currently_in_hash0
#         , crucible_struct
#           [ crucible_struct
#             [ crucible_struct
#               [ crucible_term h0
#               , crucible_term Nl0
#               , crucible_term Nh0
#               , crucible_struct [ crucible_term u0 ]
#               , crucible_term num0
#               , crucible_term md_len0
#               ]
#             ]
#           ]
#         ]);
#     let st = {{
#       { h = h0
#       , Nl = Nl0
#       , Nh = Nh0
#       , u = u0
#       , num = num0
#       , md_len = md_len0
#       }
#     }};
#     return (st, currently_in_hash0);
# };


def setup_hash_state(c : Contract, pstate : SetupVal) -> Tuple[Any, FreshVar]:
    alg0 = c.fresh_var(i32, "alg")
    h0 = c.fresh_var(array_ty(8, i64), "h0")
    Nl0 = c.fresh_var(i64, "Nl")
    Nh0 = c.fresh_var(i64, "Nh")
    u0 = c.fresh_var(array_ty(16, i64), "u")
    num0 = c.fresh_var(i32, "h0")
    is_ready_for_input0 = c.fresh_var(i8, "is_ready_for_input")
    currently_in_hash0 = c.fresh_var(i64, "currently_in_hash")
    md_len0 = c.fresh_var(i32, "md_len")
    (_, pimpl) = ptr_to_fresh(c, alias_ty('struct.s2n_hash'), "impl", read_only=True)
    c.points_to(pstate, 
        struct(
            pimpl,
            alg0,
            is_ready_for_input0,
            currently_in_hash0,
            struct(struct(struct(h0, Nl0, Nh0, struct(u0), num0, md_len0))
            )))
    # BOOKMARK
#     let st = {{
#       { h = h0
#       , Nl = Nl0
#       , Nh = Nh0
#       , u = u0
#       , num = num0
#       , md_len = md_len0
#       }
#     }};
#     return (st, currently_in_hash0);

# let update_hash_state pstate st = do {
#     alg <- crucible_fresh_var "alg" (llvm_int 32);
#     is_ready_for_input <- crucible_fresh_var "is_ready_for_input" (llvm_int 8);
#     currently_in_hash <- crucible_fresh_var "currently_in_hash" (llvm_int 64);
#     (_, pimpl) <- ptr_to_fresh_readonly "impl" (llvm_alias "struct.s2n_hash");

#     crucible_points_to pstate
#       (crucible_struct
#         [ pimpl
#         , crucible_term alg
#         , crucible_term is_ready_for_input
#         , crucible_term currently_in_hash
#         , crucible_struct
#           [ crucible_struct
#             [ crucible_struct
#               [ crucible_term {{ st.h }}
#               , crucible_term {{ st.Nl }}
#               , crucible_term {{ st.Nh }}
#               , crucible_struct [ crucible_term {{ st.u }} ]
#               , crucible_term {{ st.num }}
#               , crucible_term {{ st.md_len }}
#               ]
#             ]
#           ]
#         ]);
# };

# let hash_init_spec = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (st0, _) <- setup_hash_state pstate;
#     alg <- crucible_fresh_var "alg" (llvm_int 32);
#     crucible_execute_func [pstate, crucible_term alg];
#     // We need to pass in the starting state since many of the bits in
#     // the union are unused by many of the hash algorithms.
#     let st1 = {{ hash_init_c_state st0 }};
#     update_hash_state pstate st1;
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_reset_spec = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (st0, _) <- setup_hash_state pstate;
#     crucible_execute_func [pstate];
#     let st1 = {{ hash_init_c_state st0 }};
#     update_hash_state pstate st1;
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_copy_spec = do {
#     pstate1 <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     pstate2 <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (st1, _) <- setup_hash_state pstate1;
#     (st2, _) <- setup_hash_state pstate2;
#     crucible_execute_func [pstate1, pstate2];
#     update_hash_state pstate1 st2;
#     update_hash_state pstate2 st2;
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_update_spec msg_size = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (msg, pmsg) <- ptr_to_fresh_readonly "msg" (llvm_array msg_size (llvm_int 8));
#     (st0, _) <- setup_hash_state pstate;
#     let size = crucible_term {{ `msg_size : [32] }};
#     crucible_execute_func [pstate, pmsg, size];
#     let st1 = {{ hash_update_c_state`{msg_size=msg_size} st0 msg }};
#     update_hash_state pstate st1;
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_update_unbounded_spec = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (st0, _) <- setup_hash_state pstate;

#     size <- crucible_fresh_var "size" (llvm_int 32);
#     pmsg <- crucible_symbolic_alloc true 1 {{ (0 # size) : [64] }};
#     msg <- crucible_fresh_cryptol_var "msg" {| ByteArray |};
#     crucible_points_to_array_prefix pmsg msg {{ (0 # size) : [64] }};

#     crucible_execute_func [pstate, pmsg, (crucible_term size)];

#     let st1 = {{ hash_update_c_state_unbounded st0 msg size }};
#     update_hash_state pstate st1;

#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_digest_spec digest_size = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     (dgst, pdgst) <- ptr_to_fresh "out" (llvm_array digest_size (llvm_int 8));
#     (st0, _) <- setup_hash_state pstate;
#     size <- crucible_fresh_var "size" (llvm_int 32);
#     crucible_execute_func [pstate, pdgst, crucible_term size];
#     update_hash_state pstate st0;
#     let out1 = {{ hash_digest_c_state`{digest_size=digest_size} st0 }};
#     crucible_points_to pdgst (crucible_term out1);
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hash_get_currently_in_hash_total_spec = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hash_state");
#     pout <- crucible_alloc (llvm_int 64);
#     (st0, currently_in_hash) <- setup_hash_state pstate;
#     crucible_execute_func [pstate, pout];
#     update_hash_state pstate st0;
#     crucible_points_to pout (crucible_term {{zero: [64]}} );
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# ////////////////////////////////////////////////////////////////
# // HMAC.

# let setup_hmac_state alg0 hash_block_size0 block_size0 digest_size0 = do {
#     pstate <- crucible_alloc (llvm_alias "struct.s2n_hmac_state");
#     currently_in_hash_block0 <- crucible_fresh_var "currently_in_hash_block" (llvm_int 32);
#     xor_pad0 <- crucible_fresh_var "xor_pad" (llvm_array 128 (llvm_int 8));
#     let digest_size = eval_size {| SHA512_DIGEST_LENGTH |};
#     digest_pad0 <- crucible_fresh_var "digest_pad" (llvm_array digest_size (llvm_int 8));

#     crucible_points_to (crucible_field pstate "alg") (crucible_term alg0);
#     crucible_points_to (crucible_field pstate "hash_block_size") (crucible_term hash_block_size0);
#     crucible_points_to (crucible_field pstate "currently_in_hash_block") (crucible_term currently_in_hash_block0);
#     crucible_points_to (crucible_field pstate "xor_pad_size") (crucible_term block_size0);
#     crucible_points_to (crucible_field pstate "digest_size") (crucible_term digest_size0);
#     (inner0, _) <- setup_hash_state (crucible_field pstate "inner");
#     (inner_just_key0, _) <- setup_hash_state (crucible_field pstate "inner_just_key");
#     (outer_just_key0, _) <- setup_hash_state (crucible_field pstate "outer_just_key");
#     (outer0, _) <- setup_hash_state (crucible_field pstate "outer");
#     crucible_points_to (crucible_field pstate "xor_pad") (crucible_term xor_pad0);
#     crucible_points_to (crucible_field pstate "digest_pad") (crucible_term digest_pad0);

#     let st0 = {{
#         { alg                     = alg0
#         , hash_block_size         = hash_block_size0
#         , currently_in_hash_block = currently_in_hash_block0
#         , block_size              = block_size0
#         , digest_size             = digest_size0
#         , inner                   = inner0
#         , inner_just_key          = inner_just_key0
#         , outer                   = outer0
#         , outer_just_key          = outer_just_key0
#         , xor_pad                 = xor_pad0
#         , digest_pad              = digest_pad0
#         }
#       }};
#     return (pstate, st0);
# };

# let check_hmac_state pstate st = do {
#     crucible_points_to (crucible_field pstate "alg") (crucible_term {{ st.alg }});
#     crucible_points_to (crucible_field pstate "hash_block_size") (crucible_term {{ st.hash_block_size }});
#     crucible_points_to (crucible_field pstate "currently_in_hash_block") (crucible_term {{ st.currently_in_hash_block }});
#     crucible_points_to (crucible_field pstate "xor_pad_size") (crucible_term {{ st.block_size }});
#     crucible_points_to (crucible_field pstate "digest_size") (crucible_term {{ st.digest_size }});
#     update_hash_state (crucible_field pstate "inner") {{ st.inner }};
#     update_hash_state (crucible_field pstate "inner_just_key") {{ st.inner_just_key }};

#     // XXX: Don't care about 'outer' because it gets overwritten by
#     // 's2n_hash_reset' before use in 's2n_hmac_digest'.
#     //
#     //update_hash_state (crucible_elem pstate 7) {{ st.outer }};
#     update_hash_state (crucible_field pstate "outer_just_key") ({{ st.outer_just_key }});
#     crucible_points_to (crucible_field pstate "xor_pad") (crucible_term {{ st.xor_pad }});

#     // Don't care about 'digest_pad', because it gets overwritten
#     // using 's2n_hash_digest' before use in 's2n_hmac_digest'.
#     //
#     // However, if we leave it in, the proof still goes through
#     // (since we model exactly what happens).
#     //
#     //crucible_points_to (crucible_elem pstate 9) (crucible_term {{ st.digest_pad }});
# };

# let hmac_invariants
#       st
#       (cfg : { name            : String
#              , hmac_alg        : Term
#              , digest_size     : Int
#              , block_size      : Int
#              , hash_block_size : Int
#              }) = do {
#     // Specify the HMAC algorithm.
#     crucible_equal (crucible_term {{ st.alg }}) (crucible_term cfg.hmac_alg);

#     // Specify sizes
#     let hash_block_size = cfg.hash_block_size;
#     let block_size = cfg.block_size;
#     let digest_size = cfg.digest_size;
#     crucible_equal (crucible_term {{ st.hash_block_size }}) (crucible_term {{ `hash_block_size : [16] }});
#     crucible_equal (crucible_term {{ st.block_size }}) (crucible_term {{ `block_size : [16] }});
#     crucible_equal (crucible_term {{ st.digest_size }}) (crucible_term {{ `digest_size : [8] }});
# };

# ////////////////////////////////////////////////////////////////

# let hmac_init_spec
#       (cfg : { name            : String
#              , hmac_alg        : Term
#              , digest_size     : Int
#              , block_size      : Int
#              , hash_block_size : Int
#              }) = do {
#     alg0 <- crucible_fresh_var "alg" (llvm_int 32);
#     hash_block_size0 <- crucible_fresh_var "hash_block_size" (llvm_int 16);
#     block_size0 <- crucible_fresh_var "block_size" (llvm_int 16);
#     digest_size0 <- crucible_fresh_var "digest_size" (llvm_int 8);
#     (pstate, st0) <- setup_hmac_state alg0 hash_block_size0 block_size0 digest_size0;

#     klen <- crucible_fresh_var "klen" (llvm_int 32);
#     pkey <- crucible_symbolic_alloc true 1 {{ (0 # klen) : [64] }};
#     key <- crucible_fresh_cryptol_var "key" {| ByteArray |};
#     crucible_points_to_array_prefix pkey key {{ (0 # klen) : [64] }};

#     crucible_execute_func [pstate, crucible_term (cfg.hmac_alg), pkey, (crucible_term klen)];

#     let block_size      = cfg.block_size;
#     let hash_block_size = cfg.hash_block_size;
#     let digest_size     = cfg.digest_size;
#     let alg0            = cfg.hmac_alg;

#     let st1 = {{
#       hmac_init_c_state_unbounded
#         `{block_size=block_size
#          ,hash_block_size=hash_block_size
#          ,digest_size=digest_size}
#         st0 alg0 key klen
#     }};
#     check_hmac_state pstate st1;
#     hmac_invariants st1 cfg;
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hmac_update_spec
#       (cfg : { name            : String
#              , hmac_alg        : Term
#              , digest_size     : Int
#              , block_size      : Int
#              , hash_block_size : Int
#              }) = do {
#     let digest_size = cfg.digest_size;
#     let block_size = cfg.block_size;
#     let hash_block_size = cfg.hash_block_size;
#     (pstate, st0) <- setup_hmac_state
#                        cfg.hmac_alg
#                        {{ `hash_block_size : [16] }}
#                        {{ `block_size : [16] }}
#                        {{ `digest_size : [8] }};

#     hmac_invariants st0 cfg;

#     size <- crucible_fresh_var "size" (llvm_int 32);
#     pmsg <- crucible_symbolic_alloc true 1 {{ (0 # size) : [64] }};
#     msg <- crucible_fresh_cryptol_var "msg" {| ByteArray |};
#     crucible_points_to_array_prefix pmsg msg {{ (0 # size) : [64] }};

#     crucible_execute_func [pstate, pmsg, (crucible_term size)];

#     let st1 = {{ hmac_update_c_state_unbounded st0 msg size }};
#     check_hmac_state pstate st1;
#     hmac_invariants st1 cfg;

#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hmac_digest_spec
#       (cfg : { name            : String
#              , hmac_alg        : Term
#              , digest_size     : Int
#              , block_size      : Int
#              , hash_block_size : Int
#              }) = do {
#     (out, pout) <- ptr_to_fresh "out" (llvm_array cfg.digest_size (llvm_int 8));

#     let digest_size = cfg.digest_size;
#     let block_size = cfg.block_size;
#     let hash_block_size = cfg.hash_block_size;
#     (pstate, st0) <- setup_hmac_state
#                        cfg.hmac_alg
#                        {{ `hash_block_size : [16] }}
#                        {{ `block_size : [16] }}
#                        {{ `digest_size : [8] }};

#     hmac_invariants st0 cfg;

#     let hash_block_size = cfg.hash_block_size;
#     let block_size = cfg.block_size;
#     let digest_size = cfg.digest_size;
#     let size = {{ `digest_size : [32] }};
#     crucible_execute_func [pstate, pout, crucible_term size];
#     let st1_digest = {{
#       hmac_digest_c_state`{block_size=block_size,digest_size=digest_size} st0
#     }};
#     let st1 = {{ st1_digest.0 }};
#     let digest = {{ split (st1_digest.1) : [digest_size][8] }};

#     crucible_points_to pout (crucible_term digest);
#     crucible_return (crucible_term {{ 0 : [32] }});
# };

# let hmac_digest_size_spec
#       (cfg : { name            : String
#              , hmac_alg        : Term
#              , digest_size     : Int
#              , block_size      : Int
#              , hash_block_size : Int
#              }) = do {
#     psize <- crucible_alloc (llvm_int 8);
#     crucible_execute_func [crucible_term cfg.hmac_alg, psize];
#     let digest_size = cfg.digest_size;
#     crucible_points_to psize (crucible_term {{ `digest_size : [8] }});
#     crucible_return (crucible_term {{ 0 : [32] }});
# };
