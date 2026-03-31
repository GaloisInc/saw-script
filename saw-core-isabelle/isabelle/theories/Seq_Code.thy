theory Seq_Code
  imports WordSeq Hex_Seq WordSeq0 ZInt_Code "HOL-Library.Code_Target_Numeral"
begin

context notes [[typedef_overloaded=true]] begin
datatype ('a,'b) seqI = SeqList (proj_list : "'b list") | SeqWord (proj_word : "('a len) word")
end
lemmas [relator_eq] = seqI.rel_eq

definition int_to_bl :: "nat \<Rightarrow> int \<Rightarrow> 'b list" where
  "int_to_bl n w \<equiv> if n = 0 then [] else of_bool_list (bin_to_bl n w)"

lemma int_to_bl_length[unconstrain, simp]: "length (int_to_bl n i :: 'b :: bool list) = n"
  by (simp add: int_to_bl_def del: bin_to_bl_def)

lemma int_to_bl_0_nil[simp]: "(int_to_bl 0) = (\<lambda>_. [])"
  apply (rule ext)
  by (simp add: int_to_bl_def[abs_def])

definition bl_to_int :: "'b list \<Rightarrow> int" where
  "bl_to_int bl \<equiv> if length bl = 0 then 0 else bl_to_bin (bool_list_of bl)"

lemma bl_to_int0[simp]: "bl_to_int ([] :: 'b list) = 0"
  by (simp add: bl_to_int_def)

definition word_to_bl :: "'a :: len word \<Rightarrow> 'b list" where
  "word_to_bl w \<equiv> of_bool_list (to_bl w)"

definition bl_to_word :: "'b list \<Rightarrow> 'a :: len word" where
  "bl_to_word bl \<equiv> if length bl = 0 then 0 else of_bl (bool_list_of bl)"


definition bl_to_word0 :: "'b list \<Rightarrow> ('a len) word" where
  "bl_to_word0 bl \<equiv> if LEN('a) = 0 then 0 else bl_to_word bl"

lemma bl_to_word0_len[simp]: "LEN('a) > 0 \<Longrightarrow> bl_to_word0 = (bl_to_word  :: 'b list \<Rightarrow> ('a len) word)"
  apply (rule ext)
  by (simp add: bl_to_word0_def)                                            

lemma bl_to_word0_zero[simp]: "LEN('a) = 0 \<Longrightarrow> bl_to_word0 = (\<lambda>_. (0 :: ('a len) word))"
  apply (rule ext)
  by (simp add: bl_to_word0_def)

lemma bl_to_word_nil_0[unconstrain,simp]: "bl_to_word ([] :: 'b :: bool list) = 0"
  by (simp add: bl_to_word_def)

lemma bl_to_word0_nil_0[unconstrain,simp]: "bl_to_word0 ([] :: 'b :: bool list) = 0"
  by (simp add: bl_to_word0_def)

definition word_to_bl0 :: "('a len) word \<Rightarrow> 'b list" where
  "word_to_bl0 w \<equiv> if LEN('a) = 0 then [] else word_to_bl w"
  

lemma word_to_bl0_len[simp]: "LEN('a) > 0 \<Longrightarrow> (word_to_bl0 :: ('a len) word \<Rightarrow> 'b list) = word_to_bl"
  apply (rule ext)
  by (simp add: word_to_bl0_def)

lemma word_to_bl0_zero[simp]: "LEN('a) = 0 \<Longrightarrow> (word_to_bl0 :: ('a len) word \<Rightarrow> 'b list) = (\<lambda>_. [])"
  apply (rule ext)
  by (simp add: word_to_bl0_def)

lemma word_to_bl_transfer[transfer_rule]:
  "(pcr_word ===> (=)) (int_to_bl LENGTH('a)) (word_to_bl :: 'a :: len word \<Rightarrow> 'b list)"
  apply (rule rel_funI)+
  apply (simp add: pcr_word_def cr_word_def relcompp_apply word_to_bl_def int_to_bl_def
              del: bin_to_bl_def)
  apply transfer
  by simp

lemma word_to_bl0_transfer[transfer_rule]:
  "(pcr_word ===> (=)) (int_to_bl LEN('a)) (word_to_bl0 :: ('a len) word \<Rightarrow> 'b list)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply simp
    apply (subst len_wrapped_itself[symmetric])
    by (rule word_to_bl_transfer)
  apply (rule H;simp)
  subgoal premises prems 
    by transfer_prover
  done


lemma bl_to_word_transfer[transfer_rule]:
  "((=) ===> pcr_word) bl_to_int (bl_to_word :: 'b list \<Rightarrow> 'a :: len word)"
  apply (rule rel_funI)+
  apply (simp add: pcr_word_def cr_word_def relcompp_apply bl_to_word_def bl_to_int_def)
  apply transfer
  by simp

lemma bl_to_word0_transfer[transfer_rule]:
  "((=) ===> pcr_word) (\<lambda>xs. take_bit LEN('a) (bl_to_int xs)) (bl_to_word0 :: 'b list \<Rightarrow> ('a len) word)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (rule rel_funI)+
    apply (simp add: pcr_word_def cr_word_def relcompp_apply bl_to_word_def bl_to_int_def)
    apply transfer
    by simp
  apply (rule H;simp)
  subgoal premises prems 
    by transfer_prover
  done

lemma bl_to_from_word[unconstrain,simp]:
  "length bl = LEN('a::len) \<Longrightarrow> word_to_bl (bl_to_word bl :: 'a word) = (bl :: 'b :: bool list)"
  unfolding word_to_bl_def bl_to_word_def
  apply simp
  by (metis length_map list.map_comp list.map_id
      of_bool_of_comp to_bl_use_of_bl word_bl_Rep')

lemma bl_to_word_bool_def[unconstrain]:
  "bl_to_word (bl :: 'b :: bool list) = of_bl (map bool_of bl)"
  by (simp add: bl_to_word_def)

lemma word_from_to_bl[unconstrain, simp]:
  "bl_to_word (word_to_bl w :: 'b :: bool list) = w"
  unfolding word_to_bl_def bl_to_word_def
  by simp

lemma word_from_to_bl_cast[unconstrain, simp]:
  "bl_to_word (word_to_bl w :: 'b :: bool list) = ucast w"
  unfolding word_to_bl_def bl_to_word_def
  by (simp add: ucast_bl)

lemma bl_to_from_word0[unconstrain, simp]:
  "length xs = LEN('a) \<Longrightarrow> word_to_bl0 (bl_to_word0 xs :: ('a len) word) = (xs :: 'b :: bool list)"
  by (cases "LEN('a) > 0";simp)

lemma word_from_to_bl0_if[unconstrain, simp]:
  "bl_to_word0 (word_to_bl0 (w :: ('a len) word) :: 'b :: bool list) = (if LEN('a) > 0 then w else 0)"
  by (cases "LEN('a) > 0";simp)

lemma word_to_bl_bool_def[unconstrain]:
  "word_to_bl w = map (of_bool :: bool \<Rightarrow> 'b :: bool) (to_bl w)"
  by (simp add: word_to_bl_def)

lemma word_to_bl_length[unconstrain,simp]:
  "length (word_to_bl (w :: 'a::len word) :: 'b::bool list) = LEN('a)"
  by (simp add: word_to_bl_def)

lemma word_to_bl0_length[unconstrain,simp]:
  "length (word_to_bl0 (w :: ('a len) word) :: 'b :: bool list) = LEN('a)"
  by (cases "LEN('a) > 0";simp)


lemma bl_to_word_pos_elim[elim]:
  "0 < (bl_to_word xs :: 'a :: len word) \<Longrightarrow> (length xs > 0 \<Longrightarrow> (0 :: 'a word) < of_bl (bool_list_of xs) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases xs;simp add: bl_to_word_def)

lemma bl_to_word0_pos_elim[elim!]:
  "0 < (bl_to_word0 xs :: ('a len) word) \<Longrightarrow> (LEN('a) > 0 \<Longrightarrow> 0 < (bl_to_word xs :: ('a len) word) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases "0 < LEN('a)";simp)

definition from_seqI :: "('a,'b) seqI \<Rightarrow> 'b list" where
  "from_seqI x \<equiv> case x of 
       SeqList xs \<Rightarrow> xs 
     | SeqWord w \<Rightarrow> word_to_bl0 w"

definition seqI_valid :: "('a,'b) seqI \<Rightarrow> bool" where
  "seqI_valid x \<equiv> case x of 
      SeqList xs \<Rightarrow> length xs = LEN('a) \<and> (\<not> (is_bool TYPE('b)))
    | SeqWord w \<Rightarrow> (is_bool TYPE('b) \<and> (LEN('a) = 0 \<longrightarrow> w = 0))"


lemma seqI_validE[elim!]:
  assumes A: "seqI_valid (y :: ('a,'b) seqI)"
    and B: "(\<And>xs. y = SeqList xs \<Longrightarrow> length xs = LEN('a) \<Longrightarrow> \<not>is_bool TYPE('b) \<Longrightarrow>  P)"
    and C: "(\<And>w. y = SeqWord w \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> LEN('a) > 0 \<Longrightarrow> P)"
    and D: "y = SeqWord 0 \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> LEN('a) = 0 \<Longrightarrow> P"
  shows "P"
  supply seqI_valid_def[simp]
  apply (insert A)
  apply (cases "is_bool TYPE('b)"; cases "LEN('a) > 0"; cases y; simp)
     apply (erule(2) C)
    apply (erule(2) D)
   apply (erule(2) B)
  apply (rule B;simp)
  done


lemma seqI_validI[intro!]:
  assumes A:"\<And>xs. y = SeqList xs \<Longrightarrow> \<not> is_bool TYPE('b)"
  assumes B:"\<And>xs. y = SeqList xs \<Longrightarrow> \<not> is_bool TYPE('b) \<Longrightarrow> length xs = LEN('a)"
  assumes C:"\<And>w. y = SeqWord w \<Longrightarrow> is_bool TYPE('b)"
  assumes D:"\<And>w. y = SeqWord w \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> w > 0 \<Longrightarrow> LEN('a) > 0"
  assumes E:"\<And>w. y = SeqWord w \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> LEN('a) = 0 \<Longrightarrow> w = 0"

  shows "seqI_valid (y :: ('a,'b) seqI)"
  supply seqI_valid_def[simp]
  apply (cases "is_bool TYPE('b)"; cases "LEN('a) > 0"; cases y; simp)
  by (drule A B C D E;force)+

definition to_seqI :: "'b list \<Rightarrow> ('a,'b) seqI" where
  "to_seqI xs \<equiv> if is_bool TYPE('b) then SeqWord (bl_to_word0 xs) else SeqList (list_len LEN('a) xs)"

lemma from_to_seqI[simp]: "seqI_valid xs \<Longrightarrow> to_seqI (from_seqI xs) = xs"
  by (auto simp: to_seqI_def from_seqI_def)

lemma to_from_seqI[simp]: "length xs = LEN('a) \<Longrightarrow> from_seqI (to_seqI xs :: ('a,'b) seqI) = xs"
  by (auto simp: to_seqI_def from_seqI_def)

lemma to_seqI_valid[simp]: "seqI_valid (to_seqI xs :: ('a,'b) seqI)"
  by (simp add: to_seqI_def seqI_valid_def) 

lemma from_seqI_length[simp]: "seqI_valid (s :: ('a,'b) seqI) \<Longrightarrow> length (from_seqI s) = LEN('a)"
  by (auto simp: from_seqI_def)

typedef (overloaded) ('a,'b) seqE = "{s :: ('a,'b) seqI. seqI_valid s}"
  apply (rule exI[of _ "to_seqI (replicate LEN('a) undefined)"])
  by simp

instantiation seqE :: (_,_) not_bool begin
definition "is_bool0_seqE (_ :: ('a,'b) seqE itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_seqE_def])
end
interpretation not_bool_code "TYPE(('a,'b) seqE)" .

definition seqI_to_seqE :: "('a,'b) seqI \<Rightarrow> ('a,'b) seqE" where
  "seqI_to_seqE x \<equiv> Abs_seqE (to_seqI (from_seqI x))"

definition seqE_to_seqI :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqI" where
  "seqE_to_seqI x \<equiv> to_seqI (from_seqI (Rep_seqE x))"

interpretation seqE: 
  type_definition seqE_to_seqI "seqI_to_seqE :: ('a,'b)  seqI \<Rightarrow> ('a,'b) seqE" "{s. seqI_valid s}"
  apply (rule type_definition.intro)
  unfolding seqI_to_seqE_def seqE_to_seqI_def
  apply simp
  subgoal for x
    apply (induct x rule: Abs_seqE_induct)
    by (simp add: Abs_seqE_inverse)
  by (simp add: Abs_seqE_inverse)

setup_lifting seqE.td_thm

definition seqI_map :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a,'b) seqI \<Rightarrow> ('a,'c) seqI" where
  "seqI_map f s \<equiv> case s of
    (SeqList xs) \<Rightarrow> if is_bool TYPE('c) then 
       SeqWord (bl_to_word0 (map f xs)) else
       SeqList (map f xs)
  | (SeqWord w) \<Rightarrow> if is_bool TYPE('c)  then 
       SeqWord (bl_to_word0 (map f (word_to_bl0 w))) else 
       SeqList (map f (word_to_bl0 w))"

context includes Seq.seq.lifting begin
lift_definition seqE_to_seq :: "('a,'b) seqE \<Rightarrow> ('a,'b) seq" is
  "from_seqI"
  by simp

lift_definition seq_to_seqE :: "('a,'b) seq \<Rightarrow> ('a,'b) seqE" is
  "to_seqI"
  by simp

lift_definition map_seqE :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a,'b) seqE \<Rightarrow> ('a,'c) seqE" is
  "seqI_map"
  by (auto simp: seqI_map_def split: if_splits)
  
end

instantiation seqE :: (_,equal) equal begin
lift_definition equal_seqE :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqE \<Rightarrow> bool" is
  "HOL.equal" .
instance
  apply standard
  by (simp add: equal_seqE_def equal_eq)
end

lemma seq_to_seqE_code[code abstype]: "seqE_to_seq (seq_to_seqE x) = x"
  by transfer simp

lemma seqE_map_code[code abstract]: "seq_to_seqE (map_seq f x) = map_seqE f (seq_to_seqE x)"
  apply transfer
  by (auto simp add: seqI_map_def to_seqI_def )

lift_definition
  seqE_to_word :: "('a,'b) seqE \<Rightarrow> ('a len) word" is
  "proj_word" .


lift_definition
  word_to_seqE :: "('a len) word \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>xs. if \<not> is_bool TYPE('b) then (SeqList (list_len LEN('a) undefined)) else 
        (if LEN('a) > 0 then SeqWord xs else SeqWord 0)"
  by (auto)

lemma "seqI_valid (SeqWord (bl_to_word (seq_to_list (x :: ('a::len,'b::bool) seq)) :: ('a len) word) :: ('a,'b) seqI)"
  by auto

lemma seq_to_list_bl_to_word: "seq_to_word x = bl_to_word (seq_to_list x :: 'c :: bool list)"
  by (simp add: bl_to_word_def seq_to_list_to_word)

lemma to_seqI0[simp]:
  "LEN('a) = 0 \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> (to_seqI xs :: ('a,'b) seqI) = SeqWord 0"
  by (simp add: to_seqI_def)

lemma seqE_to_word0[simp]: "LEN('a) = 0 \<Longrightarrow> seqE_to_word (x :: ('a,'b::bool) seqE) = 0"
  by (simp add: seqE_to_word_def seqE_to_seqI_def)

lemma seq_to_word0_code[code]: "seq_to_word0 x = seqE_to_word (seq_to_seqE x)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (simp add: seqE_to_word_def seq_to_seqE_def to_seqI_def seqI_to_seqE_def 
                     seqE_to_seqI_def from_seqI_def )
    apply (subst Abs_seqE_inverse)
    subgoal by auto
    apply (simp add: seq_to_list_bl_to_word )
    apply (simp add: bl_to_word_def)
    by (metis Seq.map_seq_code seq_to_list_conv ucast_bl
        word_bl.Rep_inverse)
  by (rule H;simp)

lemma word_to_seq0_code[code abstract]: "seq_to_seqE (word_to_seq0 w) = word_to_seqE w"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_to_seqE_def seq_to_seqE_def to_seqI_def seqI_to_seqE_def 
                     seqE_to_seqI_def from_seqI_def )
    apply (subst seq_to_list_bl_to_word[symmetric])
    by simp
  apply (rule H;simp)
  unfolding seqI_to_seqE_def word_to_seqE_def seq_to_seqE_def word_to_seq0_def
            to_seqI_def
  by simp

lemma seq_to_word_code[code]: "seq_to_word x = ucast (seq_to_word0 x)"
  by (simp add: is_up.rep_eq ucast_up_ucast_id)

lemma word_to_seq_code[code]: "word_to_seq x = word_to_seq0 (ucast x)"
  apply simp
  by (metis seq_to_from_word0 seq_to_word0_len
      word_to_from_seq word_to_seq0_len)


lift_definition
  "list_to_seqE" :: "'b list \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>xs. if is_bool TYPE('b) then 
        (if length xs = LEN('a) then
          SeqWord (bl_to_word0 xs) else
          SeqWord (bl_to_word0 (list_len LEN('a) xs))) else 
        if length xs = LEN('a) then
           SeqList xs
        else
          SeqList (list_len LEN('a) xs)"
  by auto

lift_definition
  "seqE_to_list" :: "('a,'b) seqE \<Rightarrow> 'b list" is
  "\<lambda>xs. case xs of SeqWord w \<Rightarrow> word_to_bl0 w | SeqList xs \<Rightarrow> xs" .

lemma list_to_seq_code[code abstract]: "seq_to_seqE (list_to_seq s) = list_to_seqE s"
  apply transfer
  by (auto simp: to_seqI_def)

hide_const (open) list_len_checked

definition list_len_checked :: "'b list \<Rightarrow> 'a itself \<Rightarrow> 'b list" where
  "list_len_checked xs _ \<equiv> list_len LEN('a) xs" if "LEN('a) = length xs"
declare [[code drop: list_len_checked]]

hide_const (open) list_to_seq_checked
declare list_to_seq_check[code_unfold del]

definition list_to_seq_checked :: "'b list \<Rightarrow> ('a,'b) seq" where
  "list_to_seq_checked xs \<equiv> list_to_seq_raw (list_len_checked xs TYPE('a))"

lemma list_to_seq_checked_def2: "list_to_seq_checked xs = list_to_seq xs"
  unfolding list_to_seq_checked_def list_len_checked_def[unconstrain_def] list_to_seq_def
  by simp

lemma list_to_seq_check[code_unfold]: 
  "LEN('a) = length xs \<Longrightarrow> ((list_to_seq xs) :: ('a,'b) seq) = ((list_to_seq_checked xs) :: ('a,'b) seq)"
  unfolding list_to_seq_checked_def2
  by simp

text \<open>This is semantically equivalent to list_to_seqE, but implicitly assumes that the list length
      has already been checked.\<close>
lift_definition
  "list_to_seqE_checked" :: "'b list \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>xs. if is_bool TYPE('b) then 
        SeqWord (bl_to_word0 (list_len_checked xs TYPE('a))) else SeqList (list_len_checked xs TYPE('a))"
  by (auto simp: list_len_checked_def[unconstrain_def])

lemma list_to_seq_checked_code[code abstract]: "seq_to_seqE (list_to_seq_checked s) = list_to_seqE_checked s"
  apply (simp add: list_to_seq_checked_def2)
  apply transfer
  by (auto simp: to_seqI_def list_len_checked_def[unconstrain_def])

code_printing constant list_len_checked \<rightharpoonup> (SML) "(fn '_ => _)"

lemma list_to_seq_eqI:
  "(\<And>i. i < LEN('a) \<Longrightarrow> nth_list xs i = nth_list ys i) \<Longrightarrow> (list_to_seq xs :: ('a,'b) seq) = list_to_seq ys"
  apply transfer
  by (simp add: list_len_def)

lemma list_to_seq_eqI':
  "list_len LEN('a) xs = list_len LEN('a) ys \<Longrightarrow> (list_to_seq xs :: ('a,'b) seq) = list_to_seq ys"
  apply transfer
  by (simp add: list_len_def)

lemma "i < LEN('a) \<Longrightarrow> nth_list (word_to_bl (bl_to_word xs)) i = nth_list (xs :: 'b :: bool list) i"
  apply (simp add: nth_list_def)
  oops

lemma seqlist_post[code_post]: "seqE_to_seq (seqI_to_seqE (SeqList xs)) = list_to_seq (xs :: 'b :: not_bool list)"
  unfolding seqI_to_seqE_def seqE_to_seqI_def to_seqI_def from_seqI_def seqE_to_seq_def
  apply simp
   apply (subst Abs_seqE_inverse)
  subgoal by auto
  apply simp
  apply transfer
  apply simp
  done

lemma len_seq_to_list_nonempty[simp]: "seq_to_list (x :: ('a::len,'b) seq) \<noteq> []"
  apply transfer
  by fastforce

lemma bl_to_word_seq[unconstrain, simp]: "bl_to_word (seq_to_list x) = seq_to_word0 x"
  unfolding bl_to_word_def
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] for x
    apply simp
     apply (subst seq_to_word_bool_of)
     apply (simp add: seq_to_word_def2 ucast_bl map_of_to_bool Seq.map_seq_code)
    by (metis len_wrapped_itself to_bl_of_bin word_bl.Rep_inverse word_of_bl)
  by (rule H;simp)

lemma bl_to_word0_seq[unconstrain, simp]: "bl_to_word0 (seq_to_list x) = seq_to_word0 x"
  by (cases "LEN('a) > 0";simp)

lemma word_to_bl_seq[unconstrain, simp]: "list_to_seq (word_to_bl x) = word_to_seq0 x"
  unfolding word_to_bl_def
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs )
    by (simp add: seq_to_word_def2 ucast_bl)
  by (rule H;simp)

lemma word_to_bl0_seq[unconstrain, simp]: 
  "list_to_seq (word_to_bl0 xs :: 'b :: bool list) = word_to_seq0 xs"
  by (cases "LEN('a) > 0";simp)
  

lemma seqword_post[code_post]: "seqE_to_seq (seqI_to_seqE (SeqWord xs) :: ('a,'b::bool) seqE) = word_to_seq0 xs"
  unfolding seqI_to_seqE_def seqE_to_seqI_def to_seqI_def from_seqI_def seqE_to_seq_def
  apply clarsimp
   apply (subst Abs_seqE_inverse)
  subgoal by auto
  by auto

lemma numeral_seqE[code_post]: "(word_to_seq0 (numeral x) :: ('a,'b::bool) seq) = numeral x"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  by (rule H;simp)

lemma one_seqE[code_post]: "(word_to_seq0 1 :: ('a,'b::bool) seq) = 1"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  by (rule H;simp)

lemma zero_seqE[code_post]: "(word_to_seq0 0 :: ('a,'b::bool) seq) = 0"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  by (rule H;simp)


lift_definition
  "upto_seqE" :: "('a,nat) seqE" is "SeqList [0..<LEN('a)]"
  by auto

lemma upto_seq[code abstract]: "seq_to_seqE upto_seq = upto_seqE"
  apply transfer
  by (simp add: to_seqI_def)


instantiation seqI :: (_,zero) shift_ops begin
definition
  "left_shift_nat_seqI" :: "('a,'b) seqI \<Rightarrow> nat \<Rightarrow> ('a,'b) seqI" where
  "left_shift_nat_seqI xs n \<equiv> case xs of
    SeqList ys \<Rightarrow> SeqList (left_shift_nat ys n)
  | SeqWord w \<Rightarrow> SeqWord (left_shift_nat w n)"

definition
  "right_shift_nat_seqI" :: "('a,'b) seqI \<Rightarrow> nat \<Rightarrow> ('a,'b) seqI" where
  "right_shift_nat_seqI xs n \<equiv> case xs of
    SeqList ys \<Rightarrow> SeqList (right_shift_nat ys n)
  | SeqWord w \<Rightarrow> SeqWord (right_shift_nat w n)"
instance ..
end

instantiation seqI :: (_,_) rotate_ops begin
definition
  "left_rotate_nat_seqI" :: "('a,'b) seqI \<Rightarrow> nat \<Rightarrow> ('a,'b) seqI" where
  "left_rotate_nat_seqI xs n \<equiv> case xs of
    SeqList ys \<Rightarrow> SeqList (left_rotate_nat ys n)
  | SeqWord w \<Rightarrow> SeqWord (left_rotate_nat w n)"

definition
  "right_rotate_nat_seqI" :: "('a,'b) seqI \<Rightarrow> nat \<Rightarrow> ('a,'b) seqI" where
  "right_rotate_nat_seqI xs n \<equiv> case xs of
    SeqList ys \<Rightarrow> SeqList (right_rotate_nat ys n)
  | SeqWord w \<Rightarrow> SeqWord (right_rotate_nat w n)"
instance ..
end

instantiation seqE :: (_,zero) shift_ops begin
lift_definition left_shift_nat_seqE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> ('a,'b) seqE"
  is "left_shift_nat" 
  by (auto simp: left_shift_nat_seqI_def)
lift_definition right_shift_nat_seqE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> ('a,'b) seqE"
  is "right_shift_nat" 
  by (auto simp: right_shift_nat_seqI_def)
instance ..
end


lemma rotater_nil[simp]: "rotater n [] = []"
  apply (induct n;simp)
  using rotate1_is_Nil_conv
  by fastforce

instantiation seqE :: (_,_) rotate_ops begin
lift_definition left_rotate_nat_seqE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> ('a,'b) seqE"
  is "left_rotate_nat" 
  by (auto simp: left_rotate_nat_seqI_def)
lift_definition right_rotate_nat_seqE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> ('a,'b) seqE"
  is "right_rotate_nat" 
  by (auto simp: right_rotate_nat_seqI_def)
instance ..
end

lemma seqI_valid_word[simp]: 
  "LEN('a) > 0 \<Longrightarrow> is_bool TYPE('b) \<Longrightarrow> seqI_valid (SeqWord x :: ('a,'b) seqI)"
  by auto

lemma seqI_valid_word0[simp]: 
  "is_bool TYPE('b) \<Longrightarrow> seqI_valid (SeqWord 0 :: ('a,'b) seqI)"
  by auto

lemma seqI_valid_list[simp]: 
  "\<not> is_bool TYPE('b) \<Longrightarrow> length x = LEN('a) \<Longrightarrow> seqI_valid (SeqList x :: ('a,'b) seqI)"
  by auto

lemma zero_len_trivial_seqE[simp]: 
  "LEN('a) = 0 \<Longrightarrow> (x :: ('a,'b) seqE) = y"
  apply (rule seqE.Rep_eqD)
  apply transfer
  by auto

lemma seq_to_seqE_word_transfer[transfer_rule]:
  "(eq_word_seq ===> cr_seqE) (\<lambda>x. SeqWord (ucast x)) seq_to_seqE"
  apply (rule rel_funI)+
  by (auto simp add: eq_word_seq_def cr_seqE_def seq_to_seqE_def seqE_to_seqI_def
                     to_seqI_def from_seqI_def seqI_to_seqE_def Abs_seqE_inverse)

lemma seqE_to_list_transfer[transfer_rule]: "(cr_seqE ===> (=)) from_seqI seqE_to_list"
  apply (rule rel_funI)+
  apply(simp add: cr_seqE_def)
  apply transfer
  by (auto simp: from_seqI_def)

context includes rotate_shift_syntax begin

lemma shiftl_seq0[simp]: "(shiftl_seq y x 0) = x"
  apply transfer
  by simp
  

lemma right_shift_seq_code: "seq_to_seqE (x >> n) = (seq_to_seqE x) >> n"
   apply (simp add: right_shift_def[where x="seq_to_seqE x"])
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases] for x
    apply (simp add: right_shift_seq0)
    apply (simp add: right_shift_defs)
    apply transfer
    apply (simp add: right_shift_nat_seqI_def left_shift_nat_seqI_def)
    apply transfer
    by simp
  apply (rule H;simp)
  apply (simp add: right_shift_defs)
  apply transfer
  by (auto simp add: to_seqI_def right_shift_nat_seqI_def left_shift_nat_seqI_def)


lemma left_shift_seq_code: "seq_to_seqE (x << n) = (seq_to_seqE x) << n"
  unfolding left_shift_def
  apply (rule right_shift_seq_code)
  done


lemma seq_to_seqE_right_shift_nat0[simp]: "right_shift_nat (x :: ('a,'b::zero) seqE) 0 = x"
  apply transfer
  by (auto simp add: right_shift_nat_seqI_def to_seqI_def)

lemma seq_to_seqE_left_shift_nat0[simp]: "left_shift_nat (x :: ('a,'b::zero) seqE) 0 = x"
  apply transfer
  by (auto simp add: left_shift_nat_seqI_def to_seqI_def)

lemma seq_to_seqE_right_shift0[simp]: "(x ::  ('a,'b::zero) seqE) >> 0 =  x"
  unfolding right_shift_def
  by simp

lemma seq_to_seqE_left_shift0[simp]: "seq_to_seqE x << 0 = seq_to_seqE x"
  unfolding left_shift_def
  by simp

lemma right_shift_nat_seq_code[code abstract]: 
  "seq_to_seqE (right_shift_nat x n) = right_shift_nat (seq_to_seqE x) n"
  apply (insert right_shift_seq_code[where x=x and n=n] left_shift_seq_code[where x=x and n=n])
  apply (cases n;simp add: right_shift_defs del: right_shift_nat_seq_def)
  by (metis nat_int.Rep_inverse of_nat_Suc)

lemma left_shift_nat_seq_code[code abstract]: 
  "seq_to_seqE (left_shift_nat x n) = left_shift_nat (seq_to_seqE x) n"
  apply (insert left_shift_seq_code[where x=x and n=n] left_shift_seq_code[where x=x and n=n])
  apply (cases n;simp add: left_shift_def right_shift_defs del: right_shift_nat_seq_def)
  using Suc_as_int by presburger


lemma right_rotate_seq_code: "seq_to_seqE (x >>> n) = (seq_to_seqE x) >>> n"
   apply (simp add: right_rotate_def[where x="seq_to_seqE x"])
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases] for x
    apply (simp add: right_rotate_seq0)
    apply (simp add: right_rotate_defs)
    apply transfer
    apply (simp add: right_rotate_nat_seqI_def left_rotate_nat_seqI_def)
    apply transfer
    by simp
  apply (rule H;simp)
  apply (simp add: right_rotate_defs)
  apply transfer
  by (auto simp add: to_seqI_def right_rotate_nat_seqI_def left_rotate_nat_seqI_def)


lemma left_rotate_seq_code: "seq_to_seqE (x <<< n) = (seq_to_seqE x) <<< n"
  unfolding left_rotate_def
  apply (rule right_rotate_seq_code)
  done


lemma seq_to_seqE_right_rotate_nat0[simp]: "right_rotate_nat (x :: ('a,'b) seqE) 0 = x"
  apply transfer
  by (auto simp add: right_rotate_nat_seqI_def to_seqI_def)

lemma seq_to_seqE_left_rotate_nat0[simp]: "left_rotate_nat (x :: ('a,'b) seqE) 0 = x"
  apply transfer
  by (auto simp add: left_rotate_nat_seqI_def to_seqI_def)

lemma seq_to_seqE_right_rotate0[simp]: "(x ::  ('a,'b) seqE) >>> 0 =  x"
  unfolding right_rotate_def
  by simp

lemma seq_to_seqE_left_rotate0[simp]: "seq_to_seqE x <<< 0 = seq_to_seqE x"
  unfolding left_rotate_def
  by simp

lemma right_rotate_nat_seq_code[code abstract]: 
  "seq_to_seqE (right_rotate_nat x n) = right_rotate_nat (seq_to_seqE x) n"
  apply (insert right_rotate_seq_code[where x=x and n=n] left_rotate_seq_code[where x=x and n=n])
  apply (cases n;simp add: right_rotate_defs del: right_rotate_nat_seq_def)
  by (metis nat_int.Rep_inverse of_nat_Suc)

lemma left_rotate_nat_seq_code[code abstract]: 
  "seq_to_seqE (left_rotate_nat x n) = left_rotate_nat (seq_to_seqE x) n"
  apply (insert left_rotate_seq_code[where x=x and n=n] left_rotate_seq_code[where x=x and n=n])
  apply (cases n;simp add: left_rotate_def right_rotate_defs del: left_rotate_nat_seq_def)
  
  using Suc_as_int by presburger

end

context assumes A: "LEN('a) = LEN('c)" begin
definition
  "coerce_word_len_checked" :: "('a len) word \<Rightarrow> ('c len) word" where
  "coerce_word_len_checked \<equiv> ucast"

primrec
  "coerce_seqI_len_checked" :: "('a,'b) seqI \<Rightarrow> ('c,'b) seqI" where
  "coerce_seqI_len_checked (SeqWord w) = SeqWord (coerce_word_len_checked w)"
| "coerce_seqI_len_checked (SeqList xs) = SeqList xs"

lift_definition
  "coerce_seqE_len_checked" :: "('a,'b) seqE \<Rightarrow> ('c,'b) seqE" is 
  "coerce_seqI_len_checked"
  by (auto simp: A coerce_word_len_checked_def)
end
declare [[code drop: coerce_seqI_len_checked]]
declare [[code drop: coerce_seqE_len_checked]]
code_printing constant coerce_seqI_len_checked \<rightharpoonup> (SML) "_"
code_printing constant coerce_seqE_len_checked \<rightharpoonup> (SML) "_"


(* ucast, but undefined on upcasting. This is used to match coerce_seq_len semantically, but
   shouldn't ever actually execute if coercions are used properly (between equal-length sequences). *)
definition
  coerce_word :: "'b itself \<Rightarrow> ('a len) word \<Rightarrow> ('c len) word" where
  "coerce_word _ w \<equiv> bl_to_word0 (list_len LEN('c) (word_to_bl0 w :: 'b list))"

lemma coerce_word_code[code]: "(coerce_word TYPE('b) (w :: ('a len) word) :: ('c len) word) = 
  (if LEN('a) = LEN('c) \<and> is_bool TYPE('b) then (if LEN('a) > 0 then ucast w else 0)
      else bl_to_word0 (list_len LEN('c) (word_to_bl0 w :: 'b list)))"
  by (auto simp add: coerce_word_def)


lemma coerce_word_ucast[unconstrain, simp]: "LEN('a) = LEN('c) \<Longrightarrow> LEN('a) > 0 \<Longrightarrow>
   (coerce_word TYPE('b::bool) (w :: ('a len) word) :: ('c len) word) = ucast w"
  by (simp add: coerce_word_code)
  

lemma coerce_word_transfer[transfer_rule]: 
 "(pcr_word ===> pcr_word) (\<lambda>x. bl_to_int (list_len LEN('c) (int_to_bl LEN('a) x :: 'b list))) 
            (coerce_word TYPE('b) :: ('a len) word \<Rightarrow> ('c len) word)"
  unfolding coerce_word_def
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases]
    apply simp
    apply (simp only: len_wrapped_itself[symmetric, where 'a='aa] len_wrapped_itself[symmetric, where 'a='cc])
    by transfer_prover
  by (rule H; cases "LEN('a) = 0"; cases "LEN('c) = 0"; 
    simp; (thin_tac _)+; transfer_prover)

definition
  "coerce_seqI_len" :: "('a,'b) seqI \<Rightarrow> ('c,'b) seqI" where
  "coerce_seqI_len xs \<equiv>
     if LEN('a) = LEN('c) then coerce_seqI_len_checked xs else case xs of
        SeqWord w \<Rightarrow> SeqWord (coerce_word TYPE('b) w)
      | SeqList xs \<Rightarrow> SeqList (list_len LEN('c) xs)"

lemma coerce_seqI_len_checked[code_unfold]:
  "LEN('a) = LEN('c) \<Longrightarrow> (coerce_seqI_len (x :: ('a,'b) seqI) :: ('c,'b) seqI)  = coerce_seqI_len_checked x"
  by (simp add: coerce_seqI_len_def)

lemma coerce_word_pos_elim[elim!]:
  "0 < (coerce_word b (w :: ('a len) word) :: ('c len) word) \<Longrightarrow> 
    (LEN('c) > 0 \<Longrightarrow> 0 < (coerce_word b w :: ('c len) word) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding coerce_word_def
  by auto

lemma coerce_word_to_0[simp]: 
  "LEN('c) = 0 \<Longrightarrow> coerce_word TYPE('b) (w :: ('a len) word) = (0 :: ('c len) word)"
  unfolding coerce_word_def
  by simp

lift_definition
  "coerce_seqE_len" :: "('a,'b) seqE \<Rightarrow> ('c,'b) seqE" is
  "coerce_seqI_len"
  unfolding coerce_seqI_len_def
  by (auto simp: coerce_word_len_checked_def split: if_splits)

lemma coerce_seqE_len_checked[code_unfold]:
  assumes A[transfer_rule]: "LEN('a) = LEN('c)"
  shows "(coerce_seqE_len (x :: ('a,'b) seqE) :: ('c,'b) seqE)  = coerce_seqE_len_checked x"
  apply transfer
  by (simp add: coerce_seqI_len_checked[OF A])

lemma bl_to_word0_ucast[simp]: "LEN('a) = LEN('c) \<Longrightarrow> UCAST('a len \<rightarrow> 'c len) (bl_to_word0 x) = bl_to_word0 x"
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases]
   apply simp
   apply transfer
    by (simp add: bl_to_int_def)
  by (rule H;simp)


lemma int_to_bl_take[simp]: "int_to_bl n (take_bit n i) = int_to_bl n i"
  by (clarsimp simp add: int_to_bl_def simp del: bin_to_bl_def)

lemma bl_to_int_to_bl[unconstrain,simp]: "length (xs :: 'b :: bool list) = n \<Longrightarrow> int_to_bl n (bl_to_int xs) = xs"
  apply (clarsimp simp add: int_to_bl_def bl_to_int_def simp del: bin_to_bl_def)
  by (metis bl_bin_bl length_map list.map_comp list.map_id
    of_bool_of_comp)

lemma coerce_seq_len_code[code abstract]: "seq_to_seqE (coerce_seq_len (x :: ('a,'b) seq)) = coerce_seqE_len (seq_to_seqE x)"
  apply transfer
  apply (clarsimp simp add: to_seqI_def coerce_seqI_len_def coerce_word_len_checked_def)
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply transfer
    by auto
  apply (rule H)
  by (auto simp: coerce_word_def)

(* for cryptol specs this shouldn't be required, and including it is somewhat problematic
   because it results in inefficient implementations of seq functions if they haven't been 
   properly implemented as seqE *)

lemma seq_to_list_code: "seq_to_list (xs :: ('a,'b) seq) = seqE_to_list (seq_to_seqE xs)"
  apply transfer
  by simp

lemma bl_to_word_inject: "length x \<le> LENGTH ('a) \<Longrightarrow> length (x :: 'b :: bool list) = length y \<Longrightarrow> (bl_to_word x :: 'a :: len word) = bl_to_word y \<Longrightarrow> x = y"
  apply (cases "length x = 0"; simp add: bl_to_word_def)
  apply transfer
  by (metis bintrunc_bintrunc_l bl_bin_bl length_map
      list.map_comp list.map_id of_bool_of_comp
      trunc_bl2bin_len)

lemma len_less_eq_length[simp]: "LEN('a) \<le> LENGTH('a len)"
  by (cases "LEN('a) > 0";simp)
  
lemma seq_equal_code[code]: "HOL.equal (x :: ('a,'b::equal) seq) y = HOL.equal (seq_to_seqE x) (seq_to_seqE y)"
  apply (simp add: HOL.equal_eq)
  apply (rule iffI;simp?)
  apply transfer
  apply (clarsimp simp add: to_seqI_def bl_to_word_def split: if_splits)
  apply (constrain 'b="'bb::{bool,equal}")
  subgoal H[unconstrain] for x y
    apply (rule bl_to_word_inject[where 'a="'a len"];simp)
    by (auto simp add: bl_to_word0_def split: if_splits)
  apply (rule H;assumption?)
  apply standard
  done

instantiation seqI :: (_,ord) ord  begin
definition less_eq_seqI :: "('a,'b) seqI \<Rightarrow> ('a,'b) seqI \<Rightarrow> bool" where
  "less_eq_seqI x y \<equiv> case (x,y) of
      (SeqList xs, SeqList ys) \<Rightarrow> lex_list_order xs ys
     | (SeqWord xs, SeqWord ys) \<Rightarrow> xs \<le> ys"

definition less_seqI :: "('a,'b) seqI \<Rightarrow> ('a,'b) seqI \<Rightarrow> bool" where
  "less_seqI x y \<equiv> case (x,y) of
      (SeqList xs, SeqList ys) \<Rightarrow> lex_list_order_strict xs ys
     | (SeqWord xs, SeqWord ys) \<Rightarrow> xs < ys"
instance ..
end

instantiation seqE :: (_,ord) ord  begin
lift_definition less_eq_seqE :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqE \<Rightarrow> bool" 
 is "(\<le>)" .

lift_definition less_seqE :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqE \<Rightarrow> bool" 
 is "(<)" .

instance ..
end

unconstraining of_bool begin
definition nth_seqI :: "('a,'b) seqI \<Rightarrow> nat \<Rightarrow> 'b" where
  "nth_seqI x n \<equiv> case x of
     SeqList xs \<Rightarrow> nth_list xs n
   | SeqWord xs \<Rightarrow> of_bool' (xs !! (LEN('a) - Suc n))"
end

lift_definition nth_seqE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> 'b" is
  nth_seqI .

lemma lex_list_order_strict_nil[simp]: "\<not> (lex_list_order_strict [] [])"
  by (simp add: lex_list_order_strict_def)

lemma seq_less_code[code]: "(x :: ('a,'b::ord) seq) < y = ((seq_to_seqE x) < (seq_to_seqE y))"
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_conv0)
    apply transfer
    by (simp add: less_seqI_def)
  apply (rule H)
  apply transfer
  by (auto simp add: less_seqI_def to_seqI_def)

lemma seq_less_eq_code[code]: "(x :: ('a,'b::ord) seq) \<le> y = ((seq_to_seqE x) \<le> (seq_to_seqE y))"
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_conv0)
    apply transfer
    by (simp add: less_eq_seqI_def)
  apply (rule H)
  apply transfer
  by (auto simp add: less_eq_seqI_def to_seqI_def)

lemma nth_seq_code[code]: "nth_seq (x :: ('a,'b) seq) n = (if n < LEN('a) then (nth_seqE (seq_to_seqE x) n) else oob_seq_elem x)"
  apply (cases "n < LEN('a)")
  prefer 2
   apply simp
  subgoal
    apply transfer
    by simp
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
   unfolding nth_seq0
    apply (simp split del: split_of_bool)
   apply (subst seq_to_word_bool_of)
    apply transfer
   by (simp add: comp_def nth_seqI_def)
  apply (rule H)
  apply simp
  apply transfer
  by (simp add: nth_seqI_def to_seqI_def)

lemma nth_end_seq_code[code]: "nth_end_seq (x :: ('a,'b) seq) n = (if n < LEN('a) then (nth_seqE (seq_to_seqE x) (LEN('a) - Suc n)) else oob_seq_elem (rev_seq x))"
  unfolding nth_end_seq_def2 nth_seq_code
  by simp

lemma oob_seq_elem_code[code]: "oob_seq_elem x = oob_list_elem (seqE_to_list (seq_to_seqE x))"
  by (simp add: oob_seq_elem.rep_eq seq_to_list_code)

term coerce_word
definition
  append_seqI :: "('a,'b) seqI \<Rightarrow> ('c,'b) seqI \<Rightarrow> ('d,'b) seqI" where
  "append_seqI x y \<equiv> case (x,y) of
    (SeqList xs, SeqList ys) \<Rightarrow> coerce_seqI_len (SeqList (xs @ ys) :: ('a + 'c, 'b) seqI)
  | (SeqWord w, SeqWord u) \<Rightarrow> 
      (if LEN('a) = 0 then SeqWord (coerce_word TYPE('b) u) else
       if LEN('c) = 0 then SeqWord (coerce_word TYPE('b) w) else
       if LEN('d) = LEN('a) + LEN('c) then (SeqWord (word_cat w u)) else 
       SeqWord (bl_to_word0 (list_len LEN('d) (word_to_bl0 w @ word_to_bl0 u :: 'b list))))"

lift_definition 
  append_seqE :: "('a,'b) seqE \<Rightarrow> ('c,'b) seqE \<Rightarrow> ('d,'b) seqE" is
  "append_seqI"
    by (auto simp: coerce_seqI_len_def append_seqI_def split: list.splits if_splits)

lemma ucast_bl_to_word[unconstrain, simplified len_of_alt_def2[symmetric], simp]: "LENGTH('d::len) = LENGTH('c::len) \<Longrightarrow> 
          UCAST ('c \<rightarrow> 'd) (bl_to_word (bl :: 'b :: bool list)) = bl_to_word bl"
  apply (simp add: bl_to_word_def)
  by (metis ucast_bl word_bl.Rep_inverse
      word_rev_tf)

lemma append_seq_code[code abstract]: 
  "seq_to_seqE (append_seq (x :: ('a,'b) seq) (y :: ('c,'b) seq) :: ('d,'b) seq) = (append_seqE (seq_to_seqE x) (seq_to_seqE y))"
  apply (cases "LEN('d) = LEN('a) + LEN('c)")
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'd="'dd::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases] for x y
    apply (subst append_seq_map_map[where f=bool_of and g=of_bool];simp)
    apply (simp add: append_seq_conv)
    apply transfer
    apply (clarsimp simp add: append_seqI_def bl_to_word_def word_to_bl_def comp_def)
    apply transfer
    apply simp
    done
   apply (rule H;simp)
   apply transfer
   supply [simp] = 
     to_seqI_def from_seqI_def append_seqI_def coerce_seqI_len_def 
     coerce_word_len_checked_def coerce_word_def
  subgoal by auto
  apply transfer
  by auto


lemma list_len_def2:
  "list_len n xs = (take n xs) @ map (nth_list xs) [length xs..<n]"
  apply (simp add: list_append_as_map)
  by (simp add: list_len_def)

lemma list_len_code[code]: "list_len n xs = 
   (if length xs = n then xs else (if n < length xs then take n xs else xs @ map (\<lambda>i. nth_list xs i) [length xs..<n]))"
  by (simp add: list_len_def2)


lift_definition 
  take_seqE :: "('a,'b) seqE \<Rightarrow> ('c,'b) seqE" is
  "\<lambda>x. case x of 
     SeqList xs \<Rightarrow> SeqList (list_len LEN('c) xs)
   | SeqWord w \<Rightarrow> if LEN('c) = 0 then SeqWord 0 else
       if LEN('c) \<le> LEN('a) then 
        SeqWord (ucast (drop_bit (LEN('a) - LEN('c)) w))
      else SeqWord (coerce_word TYPE('b) w)"
  by (auto split: if_splits)

lemma take_seq_code[code abstract]: 
  "seq_to_seqE (take_seq (x :: ('a,'b) seq) :: ('c,'b) seq) = (take_seqE (seq_to_seqE x))"
  supply [simp del] = bin_to_bl_def
  apply (cases "LEN('c) \<le> LEN('a)")
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: take_seq0)
    supply [transfer_rule] = coerce_seq_len_word_transfer
    apply transfer
    apply (simp add: coerce_seqI_len_def coerce_word_len_checked_def)
    apply transfer
    by auto
   apply (rule H;simp)
   apply (elim context_disjE;simp)
   apply transfer
   apply (simp add: to_seqI_def)
  apply transfer
  by (simp add: to_seqI_def coerce_word_def)

lift_definition 
  drop_seqE :: "('a,'b) seqE \<Rightarrow> ('c,'b) seqE" is
  "\<lambda>x. case x of 
     SeqList xs \<Rightarrow> SeqList (list_len LEN('c) (drop (LEN('a) - LEN('c)) xs))
   | SeqWord w \<Rightarrow> if LEN('c) = 0 then SeqWord 0 else 
     if LEN('c) \<le> LEN('a) then
      SeqWord (ucast w) else
      SeqWord (coerce_word TYPE('b) w)"
  by (auto split: if_splits)

lemma drop_seq_code[code abstract]: 
  "seq_to_seqE (drop_seq (x :: ('a,'b) seq) :: ('c,'b) seq) = (drop_seqE (seq_to_seqE x))"
  apply (cases "LEN('c) \<le> LEN('a)")
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: drop_seq0)
    supply [transfer_rule] = coerce_seq_len_word_transfer
    apply transfer
    apply simp
    apply transfer
    by simp
  subgoal
    apply (rule H;simp)
    apply transfer
    by (auto simp add: to_seqI_def)
  apply transfer
  apply (simp add: to_seqI_def)
  apply transfer
  by auto

lift_definition 
  replicate_seqE :: "'b \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>b. if is_bool TYPE('b) then 
     SeqWord (bl_to_word (replicate LEN('a) b)) else SeqList (replicate LEN('a) b)"
  by auto


lemma replicate_seq_code[code abstract]: 
  "seq_to_seqE (replicate_seq b :: ('a,'b) seq) = replicate_seqE b"
  apply transfer
  by (simp add: to_seqI_def bl_to_word0_def)

unconstraining bool_of begin
lift_definition 
  seq_updateE :: "('a,'b) seqE \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>x n b. case x of
    SeqWord w \<Rightarrow> if n < LEN('a) then SeqWord (set_bit w (LEN('a) - Suc n) (bool_of b))
     else SeqWord w
  | SeqList xs \<Rightarrow> SeqList (xs[n := b])"
  by (auto split: if_splits)
end

lemma seq_update_code[code abstract]: 
  "seq_to_seqE (seq_update x n b :: ('a,'b) seq) = seq_updateE (seq_to_seqE x) n b"
  apply (constrain 'a="'aa::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases] for x b
    apply (cases "n < LENGTH('aa)")
     apply (subst seq_update_map_map[where f=bool_of and g=of_bool];simp?)
     apply (simp add: seq_update_word_conv)
     apply transfer
     apply (simp add: comp_def set_bit_eq)
     apply transfer
     apply simp
     apply (metis bintr_bintr_i take_bit_set_bit_eq take_bit_unset_bit_eq)
    apply (simp add: seq_update_oob)
    apply transfer
    by simp
  apply (rule H;simp)
  apply transfer
  by (auto simp add: to_seqI_def)



definition
  concat_seqE :: "('n, ('m, 'b) seqE) seqE \<Rightarrow> ('k, 'b) seqE" where
  "concat_seqE xss \<equiv> if is_bool TYPE('b) \<and> LEN('k) = LEN('n) * LEN('m) then
      word_to_seqE (word_rcat (map seqE_to_word (seqE_to_list xss))) else
      list_to_seqE (concat (map seqE_to_list (seqE_to_list xss)))"

lemma seqE_to_list_map: "(seqE_to_list (map_seqE f xs)) = map f (seqE_to_list xs)"
  apply transfer
  by (auto simp: from_seqI_def seqI_map_def)

lemma seqE_to_list_seq: "(seqE_to_list (seq_to_seqE xs)) = seq_to_list xs"
  apply transfer
  by auto

lemma seq_to_seqE_via_list: "list_to_seqE (seq_to_list xs) = seq_to_seqE xs"
  apply transfer
  by (auto simp: to_seqI_def)

lemma seqE_to_word_comp_is_ucast: "(seqE_to_word \<circ> seq_to_seqE) = (\<lambda>xs. (ucast (seq_to_word xs)))"
  apply (rule ext)
  apply (simp add: comp_def)
  by (metis seq_to_word0_code seq_to_word0_len)

lemma word_rcat_map_ucast:
  "LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow> 
         word_rcat (map (\<lambda>x. UCAST('a \<rightarrow> 'b) (f x)) xs) = word_rcat (map f xs) "
  apply (simp add: word_rcat_eq)
  apply transfer
  by (simp add: comp_def)


lemma concat_seq_code[code abstract]: 
  "seq_to_seqE (concat_seq xss) = concat_seqE (seq_to_seqE (map_seq seq_to_seqE xss))"
  apply (cases "is_bool TYPE('b) \<and> LEN('a) = LEN('c) * LEN('d)")
   apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'd="'dd::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (subst coerce_concat_seq2[symmetric, where 'k="'cc \<times> 'dd"])
     apply simp
    apply (subst concat_seq_map)
    unfolding concat_seqE_def
    apply (simp add: seqE_to_list_seq map_seq_code seqE_to_word_comp_is_ucast)
    apply (simp add: word_rcat_map_ucast)
    apply (subst word_to_seq0_code[symmetric])
    apply (simp add: word_seq_convs)
    apply transfer
    by (simp add: to_bl_of_bin ucast_bl word_rcat_eq)
   apply (rule H;simp)
  unfolding concat_seqE_def
  apply (subst if_not_P,assumption)
  apply (simp add: concat_seq_def list_to_seq_code )
  by (simp add: seqE_to_list_seq map_seq_code comp_def)

declare transpose_seq_def[code]


context begin
private definition test :: "(6 / 2,int) seq" where
  "test \<equiv> coerce_seq_len ((list_to_seq [1,2,3]) :: (3,int) seq) :: (6 / 2,int) seq"
value "test"
end


instantiation seqE :: (_,zero) zero begin
lift_definition zero_seqE :: "('a,'b) seqE" is
  "if is_bool TYPE('b) then SeqWord 0 else SeqList (replicate LEN('a) 0 :: 'b list)"
  by auto
instance ..
end

lift_definition zero_seqE_bool :: "('a,'b) seqE" is
  "if is_bool TYPE('b) then SeqWord 0 else SeqList (list_len LEN('a) [])"
  by auto

lemma seq_zero_code_fwd: "0 = seqE_to_seq 0"
  apply transfer
  by (clarsimp simp: from_seqI_def word_to_bl0_def word_to_bl_def)

lemma seq_zero_code[code abstract]: "seq_to_seqE 0 = 0"
  apply (simp add: seq_zero_code_fwd)
  apply transfer
  by (auto)

context includes Seq.seq.lifting begin
lift_definition zero_seq_bool :: "('a,'b) seq" is
  "if is_bool TYPE('b) then word_to_bl0 (0 :: ('a len) word) else list_len LEN('a) []"
  by auto
end

lemma zero_seq_bool_code[code abstract]: "seq_to_seqE zero_seq_bool = zero_seqE_bool"
  apply transfer
  by (auto simp: to_seqI_def)

lemma zero_seq_bool_zero[unconstrain]: "zero_seq_bool = (0 :: ('a,'b::bool) seq)"
  by (simp add: zero_seq_bool_def zero_seq0)

instantiation seqE :: (_,bool) abs begin
lift_definition abs_seqE :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>x. SeqWord (abs (proj_word x))"
  by auto
instance ..
end

lemma msb_is_head_seqE: "msb (seqE_to_word (x :: ('a,'b::bool) seqE)) = (nth_seqE x 0 = 1)"
  apply (simp add: msb_nth)
  apply transfer
  by (auto simp: nth_seqI_def)

(* no abs implementation for word *)
lemma abs_seqE_code[code]: 
  "abs x = (if nth_seqE x 0 = 1 then word_to_seqE (-(seqE_to_word x)) else x)"
  apply (simp add: msb_is_head_seqE[symmetric])
  apply transfer
  by (auto simp add: word_abs_msb)
  
lemma abs_seq_code[code abstract]: "seq_to_seqE (abs xs) = abs (seq_to_seqE xs)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (transfer;simp)+
  by (rule H;simp)

lemma group_seq_code[code abstract]: "seq_to_seqE (group_seq (xs :: ('parts \<times> 'each, 'a) seq )) = 
  list_to_seqE (map list_to_seq (group_list LEN('parts) LEN('each) (seqE_to_list (seq_to_seqE xs))))"
  by (simp add: seqE_to_list_seq group_seq_code[symmetric] seq_to_seqE_via_list)

declare selects_seq_def2[code]

lift_definition zext_seqE :: "('a,'b::zero) seqE \<Rightarrow> ('c,'b) seqE" is
  "\<lambda>x. case x of
    SeqWord w \<Rightarrow> if LEN('c) > 0 then SeqWord (unsigned w) else SeqWord 0
  | SeqList xs \<Rightarrow> SeqList (ext_list LEN('c) 0 xs)"
  by (auto split: if_splits)

lift_definition sext_seqE :: "('a,'b::zero) seqE \<Rightarrow> ('c,'b) seqE" is
  "\<lambda>x. case x of
    SeqWord w \<Rightarrow> if LEN('c) > 0 then SeqWord (signed w) else SeqWord 0
  | SeqList xs \<Rightarrow> SeqList (sext_list LEN('c) xs)"
  by (auto split: if_splits)

lemma bl_to_word_zero[unconstrain,simp]: 
  "n = LEN('a) \<Longrightarrow> bl_to_word (replicate n 0 :: 'b:: bool list) = (0 :: 'a :: len word)"
  unfolding bl_to_word_def
  by simp


lemma zext_seq_code[code abstract]: "seq_to_seqE (zext_seq xs) = zext_seqE (seq_to_seqE xs)"
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: zext_seq0)
    apply transfer
    apply clarsimp
    apply transfer
    by simp
  apply (rule H)
  apply transfer
  by (auto simp: to_seqI_def)

lemma sext_list_empty[simp]: "(sext_list n []) = replicate n 0"
  unfolding sext_list_def sign_list_def
  by simp

lemma sext_seq_code[code abstract]: "seq_to_seqE (sext_seq xs) = sext_seqE (seq_to_seqE xs)"
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'b="'bb::bool")
  subgoal H[unconstrain_cases]
    apply (simp add: sext_seq0)
    apply transfer
    apply clarsimp
    apply transfer
    by simp
  apply (rule H)
  apply transfer
  by (auto simp: to_seqI_def)

lemma zip_seq_code[code abstract]: "seq_to_seqE (zip_seq x y) = 
  list_to_seqE (zip (seq_to_list x) (seq_to_list y))"
  apply transfer
  by (auto simp: to_seqI_def)

lemma word_reverse_zero: "word_reverse 0 = 0"
  unfolding word_reverse_def
  by simp

lift_definition rev_seqE :: "('a,'b) seqE \<Rightarrow> ('a,'b) seqE" is
  "\<lambda>x. case x of
    SeqWord w \<Rightarrow> SeqWord (word_reverse w)
  | SeqList xs \<Rightarrow> SeqList (rev xs)"
  by (auto simp: word_reverse_zero split: if_splits)

lemma rev_seq_code[code abstract]: 
  "seq_to_seqE (rev_seq x) = rev_seqE (seq_to_seqE x)"
  apply transfer
  by (auto simp: to_seqI_def word_reverse_def bl_to_word0_def 
                 bl_to_word_def word_bl.Abs_inverse rev_map)

lemma set_seq_code[code]: "set_seq y = set (seqE_to_list (seq_to_seqE y))"
  apply transfer
  by simp

experiment  begin
context includes rotate_shift_syntax and seq_syntax begin

value " ((list_to_seq [True,False,True,True]) :: (4,bool) seq)"
value "(0 ^ 10000000) :: (32, bool) seq"
value "(269 ^ 1000000) :: (128, bool) seq"
value "(269 ^ 1000000) :: 128 word"

value "(-1) :: (3,bool) seq"
value "seq_update (8 :: (3,bool) seq) 2 True"
lemma 
  "((list_to_seq [1,2]) :: (2,int) seq) << 1 = list_to_seq [2,0]"
  "((list_to_seq [True,False,True]) :: (3,bool) seq) << 1 = 2"
  "((list_to_seq [1,2]) :: (2,int) seq) <<< 1 = list_to_seq [2,1]"
  "((list_to_seq [True,False,True]) :: (3,bool) seq) <<< 1 = 3"
  "uint_seq (3 :: (8,bool) seq) = 3"
  "sint_seq ((list_to_seq [True,False,True,True]) :: (4,bool) seq) = -5"
  "(of_int_seq 3 :: (4,bool) seq) = 3"
  "((3 ^ 1000) :: (8,bool) seq) = 33"
  "(from_nat (log2_nat (to_nat (32 :: (32,bool) seq))) :: (32,bool) seq) = 5"
  "nth_seq ((list_to_seq [True,False,True]) :: (3,bool) seq) 1 = False"
  "nth_seq ((list_to_seq [True,False,True]) :: (3,bool) seq) 2 = True"
  "(coerce_seq_len ((list_to_seq [1,2,3]) :: (3,int) seq) :: (6 / 2,int) seq) = list_to_seq [1,2,3]"
  "(take_seq (list_to_seq [1,2,3,4,5] :: (5,int) seq) :: (3,int) seq) = list_to_seq [1,2,3]"
  "(take_seq (list_to_seq [True,False,True,True,True] :: (5,bool) seq) :: (3,bool) seq) = list_to_seq [True,False,True]"
  "(drop_seq (list_to_seq [1,2,3,4,5] :: (5,int) seq) :: (3,int) seq) = list_to_seq [3,4,5]"
  "(drop_seq (list_to_seq [True,False,True,True,True] :: (5,bool) seq) :: (3,bool) seq) = list_to_seq [True,True,True]"
  "carry_seq (1 :: (3,bool) seq) ((-1) :: (3,bool) seq)"
  "scarry_seq (4 :: (3,bool) seq) ((-1) :: (3,bool) seq)"
  "sborrow_seq (8 :: (3,bool) seq) (4 :: (3,bool) seq)"
  "seq_update (8 :: (3,bool) seq) 2 True = 1"
  "seq_update (list_to_seq [1,2,3] :: (3,int) seq) 1 4 = list_to_seq [1,4,3]"
  "concat_seq \<lbrakk>\<lbrakk>1::int,2\<rbrakk>,\<lbrakk>3,4\<rbrakk>,\<lbrakk>5,6\<rbrakk>\<rbrakk> = \<lbrakk>1,2,3,4,5,6\<rbrakk>"
  "concat_seq \<lbrakk>\<lbrakk>0,1\<rbrakk>,\<lbrakk>1,0\<rbrakk>,\<lbrakk>1,1\<rbrakk>\<rbrakk> = (0x1B :: [6])"
  "abs (-5 :: [32]) = 5"
  "abs (5 :: [32]) = 5"
  "rev_seq \<lbrakk>1::int,2,3\<rbrakk> = \<lbrakk>3,2,1\<rbrakk>"
  "rev_seq \<lbrakk>True,False,False\<rbrakk> = \<lbrakk>False,False,True\<rbrakk>"
  "((0x8000000000000010 :: (64,bool) seq) >>$ 5) = 0xFC00000000000000"
  "((0x80000010 :: (32,bool) seq) >>$ 5) = 0xFC000000"
  "set_seq \<lbrakk>1::int,1,2,3\<rbrakk> = {1,2,3}"
  "set_seq (0 :: (32,bool) seq) = {0}"
  "set_seq (-1 :: (32,bool) seq) = {1}"
  "set_seq (1 :: (32,bool) seq) = {0,1}"
  by eval+

value "(from_nat (log2_nat (to_nat (32 :: (32,bool) seq))) :: (32,bool) seq)"
value "((3 ^ 1000) :: (8,bool) seq)"
value "(of_int_seq 3 :: (4,bool) seq)"
value "sint_seq ((list_to_seq [True,False,True,True]) :: (4,bool) seq)"
value "uint_seq (3 :: (8,bool) seq)"
value "((list_to_seq [1,2]) :: (2,int) seq) << 1"
value "((list_to_seq [True,False,True]) :: (3,bool) seq) << 1"
value "((list_to_seq [1,2]) :: (2,int) seq) <<< 1"
value "((list_to_seq [True,False,True]) :: (3,bool) seq) <<< 1"
value "coerce ((list_to_seq [1,2]) :: (2,int) seq) :: (1+1,int) seq"

end
end

(* for seq operations without an analogous word operation, we can simply provide an implementation
   for seq_to_list which will allow the existing seq code equations to be used *)

declare seq_to_list_code[code]
declare list_to_seq_code[code]

experiment begin

lemma 
  "foldl_seq (+) 0 (list_to_seq [1,2,3,4,5] :: (5,int) seq) = 15"
  "foldl_seq (\<noteq>) 0 (list_to_seq [1,0,1,1,0] :: (5,bool) seq) = 1"
  "foldl_seq (\<noteq>) 1 (list_to_seq [1,0,1,1,0] :: (5,bool) seq) = 0"
  "scanl_seq (+) 1 (list_to_seq [1,0,1,1,0] :: (5,int) seq) = (list_to_seq [1, 2, 2, 3, 4, 4] :: (6,int) seq)"
  "scanl_seq (\<noteq>) 1 (list_to_seq [1,0,1,1,0] :: (5,bool) seq) = (list_to_seq [1, 0, 0, 1, 0, 0] :: (6,bool) seq)"
  by eval+

end

context includes Seq.seq.lifting begin

lift_definition to_bool_seq :: "('a,'b) seq \<Rightarrow> ('a,bool) seq" is "\<lambda>xs. list_len LEN('a) (bool_list_of xs)"
  by simp

lift_definition to_bool_seqE :: "('a,'b) seqE \<Rightarrow> ('a,bool) seqE" is 
  "\<lambda>x. case x of
     SeqWord w \<Rightarrow> SeqWord w
   | SeqList xs \<Rightarrow> if LEN('a) > 0 then SeqWord (of_bl (list_len LEN('a) (bool_list_of xs))) else SeqWord 0"
  by (auto split: if_splits)

lemma to_bool_seq_code[code abstract]: "seq_to_seqE (to_bool_seq xs) = to_bool_seqE (seq_to_seqE xs)"
  apply transfer
  by (auto simp: to_seqI_def bl_to_word_def)

lift_definition from_bool_seq :: "('a,bool) seq \<Rightarrow> ('a,'b) seq" is "\<lambda>xs. list_len LEN('a) (of_bool_list xs)"
  by simp

lift_definition from_bool_seqE :: "('a,bool) seqE \<Rightarrow> ('a,'b) seqE" is 
  "\<lambda>x. case x of
     SeqWord w \<Rightarrow> if is_bool TYPE('b) then SeqWord w else SeqList (list_len LEN('a) (of_bool_list (to_bl w)))"
  by (auto split: if_splits)

lemma from_bool_seq_code[code abstract]: "seq_to_seqE (from_bool_seq xs) = from_bool_seqE (seq_to_seqE xs)"
  apply transfer
  apply (clarsimp simp: to_seqI_def bl_to_word_def bl_to_word0_def to_bl_use_of_bl )
  by (metis len_wrapped_valid length_to_bl_eq to_bl_use_of_bl)

end

context
  includes state_combinator_syntax and term_syntax
begin

definition
  valterm_cons :: "('a \<times> (unit \<Rightarrow> Code_Evaluation.term))  \<Rightarrow>
    ('a :: typerep) list \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> ('a :: typerep) list \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where [code_unfold]: "valterm_cons x xs = Code_Evaluation.valtermify Cons {\<cdot>} x {\<cdot>} xs "

definition
  valterm_list_to_seq :: "('a :: typerep) list \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> ('n::typerep,'a :: typerep) seq \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where [code_unfold]: "valterm_list_to_seq xs = Code_Evaluation.valtermify list_to_seq {\<cdot>} xs"

definition
  valterm_word_to_seq :: "(('n len) word \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<Rightarrow> ('n :: typerep,'a :: typerep) seq \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where [code_unfold]: "valterm_word_to_seq xs = 
     (let j = from_bool_seq (word_to_seq0 (fst xs)) in (j, \<lambda>_. Code_Evaluation.term_of j))"

fun
  exhaust_list_n :: "('a :: full_exhaustive list \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> nat \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" where
  "exhaust_list_n f (Suc n) d = (if d < 1 then None else 
   Quickcheck_Exhaustive.full_exhaustive (\<lambda>x.
      exhaust_list_n (\<lambda>xs. f (valterm_cons x xs)) n (d-1)) d)"
| "exhaust_list_n f 0 d = f (Code_Evaluation.valtermify [])"

end

instantiation seq :: (typerep,"{typerep,full_exhaustive}") full_exhaustive begin

definition "full_exhaustive_seq" :: 
 "(('a, 'b) seq \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
   \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" where
  "full_exhaustive_seq f d \<equiv> case is_bool TYPE('b) \<and> LEN('a) > 0 of
    True \<Rightarrow> Quickcheck_Exhaustive.full_exhaustive (\<lambda>w. f (valterm_word_to_seq w)) d
  | False \<Rightarrow> exhaust_list_n (\<lambda>xs. f (valterm_list_to_seq xs)) LEN('a) (max d (natural_of_nat LEN('a)))"

instance ..
end

context
  includes state_combinator_syntax and term_syntax
begin


fun random_list_n_aux ::
  "nat \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> (('a :: random) list \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
  where
  "random_list_n_aux 0 i = Pair (Code_Evaluation.valtermify ([] :: 'a list))"
| "random_list_n_aux (Suc n) i = random_class.random i \<circ>\<rightarrow> (\<lambda>(v :: 'a \<times> (unit \<Rightarrow> term)). random_list_n_aux n i \<circ>\<rightarrow> 
     (\<lambda>(xs :: 'a list \<times> (unit \<Rightarrow> term)). Pair (valterm_cons v xs)))"

end

instantiation seq :: (typerep,"random") random begin
context
  includes state_combinator_syntax and term_syntax
begin

definition random_seq ::
  "natural \<Rightarrow> Random.seed \<Rightarrow> (('a,'b :: random) seq \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
  where
  "random_seq i \<equiv> case is_bool TYPE('b) \<and> LEN('a) > 0 of
     True \<Rightarrow> Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>x. Pair (valterm_word_to_seq x))
   | False \<Rightarrow> random_list_n_aux LEN('a) i \<circ>\<rightarrow> (\<lambda>x. Pair (valterm_list_to_seq x))"

instance ..
end
end

lemma zth_seq_code[code]:
  "zth_seq xs n = nth_seq xs (to_nat_mod_ring n)"
  apply transfer
  by simp

context includes seq_syntax begin

lemma "LEN('a) > 3 \<Longrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> zth_seq x i \<noteq> zth_seq x j \<and> zth_seq y i \<noteq> zth_seq y j) \<Longrightarrow> (x :: ('a,int) seq) = y"
  quickcheck
  quickcheck [ random]
oops

lemma "x * 2 = y div 2 \<Longrightarrow> (x :: (16,bool) seq) > y"
  quickcheck
  quickcheck [random]
  oops

lemma "(\<forall>i j. i \<noteq> j \<longrightarrow> zth_seq x i \<noteq> zth_seq x j \<and> zth_seq y i \<noteq> zth_seq y j) \<Longrightarrow> (x :: (100,int) seq) = y"
  quickcheck
  quickcheck [ random]
  oops

end

end