theory "Sequences"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition all_as_fold :: "{'n,'a} ((fin 'n) =?> (('a \<Rightarrow> Bit) \<Rightarrow> ((['n]'a) \<Rightarrow> Bit)))" where
"all_as_fold f xs \<equiv> ((all`{'n,'a} f xs) ==`{Bit} (foldl`{'n,Bit,'a} (\<lambda>(a :: Bit) (b :: 'a). (a \<and> (f`{} b))) True xs)) \<and> ((all`{'n,'a} f xs) ==`{Bit} (foldr`{'n,'a,Bit} (\<lambda>(a :: 'a) (b :: Bit). (b \<and> (f`{} a))) True xs))"

cryptol_definition any_as_fold :: "{'n,'a} ((fin 'n) =?> (('a \<Rightarrow> Bit) \<Rightarrow> ((['n]'a) \<Rightarrow> Bit)))" where
"any_as_fold f xs \<equiv> ((any`{'n,'a} f xs) ==`{Bit} (foldl`{'n,Bit,'a} (\<lambda>(a :: Bit) (b :: 'a). (a \<or> (f`{} b))) False xs)) \<and> ((any`{'n,'a} f xs) ==`{Bit} (foldr`{'n,'a,Bit} (\<lambda>(a :: 'a) (b :: Bit). (b \<or> (f`{} a))) False xs))"

cryptol_definition append_upto :: "{'n,'m,'a} ((fin 'n,fin 'm,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['m]'a) \<Rightarrow> Bit)))" where
"append_upto x y \<equiv> (map`{'n + 'm,Integer,'a} (\<lambda>(i :: Integer). (if i >=`{Integer} (number`{'n,Integer}) then (y @`{'m,'a,Integer} (i -`{Integer} (number`{'n,Integer}))) else coerce (x @`{'n,'a,Integer} i))) (fromToLessThan`{0,'n + 'm,Integer})) ==`{['n + 'm]'a} (x #`{'n,'m,'a} y)"

cryptol_definition bang_is_end :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"bang_is_end xs i \<equiv> ((0 :: Integer) <=`{Integer} i) \<longrightarrow> ((i <`{Integer} (number`{'n,Integer})) \<longrightarrow> ((xs !`{'n,'a,Integer} i) ==`{'a} (xs @`{'n,'a,Integer} (((number`{'n,Integer}) -`{Integer} i) -`{Integer} (1 :: Integer)))))"

cryptol_definition butlast :: "{'n,'a} ((fin 'n) =?> (([1 + 'n]'a) \<Rightarrow> (['n]'a)))" where
"butlast xs \<equiv> take`{'n,1,'a} xs"

cryptol_definition drop_append :: "{'front,'back,'a} ((fin 'front,fin 'back,Eq 'a) =?> ((['front]'a) \<Rightarrow> ((['back]'a) \<Rightarrow> Bit)))" where
"drop_append x y \<equiv> (drop`{'front,'back,'a} (x #`{'front,'back,'a} y)) ==`{['back]'a} y"

cryptol_definition foldl_valid :: "{'n,'k,'a,'b} ((fin 'n,'k < 'n,Eq 'a) =?> (('a \<Rightarrow> ('b \<Rightarrow> 'a)) \<Rightarrow> ('a \<Rightarrow> ((['n]'b) \<Rightarrow> Bit))))" where
"foldl_valid f x xs \<equiv> (foldl`{'n,'a,'b} f x xs) ==`{'a} (foldl`{'n - 'k,'a,'b} f (foldl`{'k,'a,'b} f x (take`{'k,'n - 'k,'b} xs)) (drop`{'k,'n - 'k,'b} xs))"

cryptol_definition foldr_valid :: "{'n,'k,'a,'b} ((fin 'n,'k < 'n,Eq 'b) =?> (('a \<Rightarrow> ('b \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> ((['n]'a) \<Rightarrow> Bit))))" where
"foldr_valid f x xs \<equiv> (foldr`{'n,'a,'b} f x xs) ==`{'b} (foldr`{'k,'a,'b} f (foldr`{'n - 'k,'a,'b} f x (drop`{'k,'n - 'k,'a} xs)) (take`{'k,'n - 'k,'a} xs))"

cryptol_definition groupBy_map :: "{'each,'parts,'a} ((fin 'each,fin 'parts,Eq 'a,Ring 'a) =?> ((['each * 'parts]'a) \<Rightarrow> Bit))" where
"groupBy_map x \<equiv> (groupBy`{'each,'parts,'a} x) ==`{['parts]['each]'a} (map`{'parts,Integer,['each]'a} (\<lambda>(p :: Integer). (map`{'each,Integer,'a} (\<lambda>(e :: Integer). (x @`{'each * 'parts,'a,Integer} ((p *`{Integer} (number`{'each,Integer})) +`{Integer} e))) (fromToLessThan`{0,'each,Integer}))) (fromToLessThan`{0,'parts,Integer}))"

cryptol_definition head_0th :: "{'n,'a} (('n > 0,fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"head_0th x \<equiv> (head`{'n - 1,'a} x) ==`{'a} (x @`{'n,'a,Integer} (0 :: Integer))"

cryptol_definition join_append :: "{'n,'m,'a} ((fin 'n,fin 'm,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['n]'a) \<Rightarrow> Bit)))" where
"join_append x y \<equiv> (join`{2,'n,'a} (list_to_seq [x : (['n]'a),y : (['n]'a)] :: [2]['n]'a)) ==`{[2 * 'n]'a} (x #`{'n,'n,'a} y)"

cryptol_definition join_map :: "{'parts,'each,'a} ((fin 'each,fin 'parts,Eq 'a,Ring 'a) =?> ((['parts]['each]'a) \<Rightarrow> Bit))" where
"join_map x \<equiv> (join`{'parts,'each,'a} x) ==`{['parts * 'each]'a} (map`{'parts * 'each,Integer,'a} (\<lambda>(n :: Integer). ((x @`{'parts,['each]'a,Integer} ((n -`{Integer} (n %`{Integer} (number`{'each,Integer}))) /`{Integer} (number`{'each,Integer}))) @`{'each,'a,Integer} (n %`{Integer} (number`{'each,Integer})))) (fromToLessThan`{0,'parts * 'each,Integer}))"

cryptol_definition join_split :: "{'parts,'each,'a} ((fin 'each,fin 'parts,Eq 'a) =?> ((['parts]['each]'a) \<Rightarrow> Bit))" where
"join_split x \<equiv> (split`{'parts,'each,'a} (join`{'parts,'each,'a} x)) ==`{['parts]['each]'a} x"

cryptol_definition last_nth :: "{'n,'a} (('n > 0,fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"last_nth x \<equiv> (last`{'n - 1,'a} x) ==`{'a} (x @`{'n,'a,Integer} ((number`{'n,Integer}) -`{Integer} (1 :: Integer)))"

cryptol_definition map_upto :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"map_upto x \<equiv> (map`{'n,Integer,'a} (\<lambda>(i :: Integer). (x @`{'n,'a,Integer} i)) (fromToLessThan`{0,'n,Integer})) ==`{['n]'a} x"

cryptol_definition map_valid :: "{'n,'a,'b} ((fin 'n,Eq 'b) =?> (('a \<Rightarrow> 'b) \<Rightarrow> ((['n]'a) \<Rightarrow> Bit)))" where
"map_valid f xs \<equiv> all`{'n,Integer} (\<lambda>(ix :: Integer). (((map`{'n,'a,'b} f xs) @`{'n,'b,Integer} ix) ==`{'b} (f`{} (xs @`{'n,'a,Integer} ix)))) (fromToLessThan`{0,'n,Integer})"

cryptol_definition product_as_fold :: "{'n,'a} ((fin 'n,Eq 'a,Ring 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"product_as_fold xs \<equiv> (product`{'n,'a} xs) ==`{'a} (foldl`{'n,'a,'a} (\<lblot>*`{'a}\<rblot>) (fromInteger`{'a} (1 :: Integer)) xs)"

cryptol_definition reverse_nth :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"reverse_nth x i \<equiv> (((0 :: Integer) <=`{Integer} i) \<and> (i <`{Integer} (number`{'n,Integer}))) \<longrightarrow> ((x @`{'n,'a,Integer} i) ==`{'a} ((reverse`{'n,'a} x) @`{'n,'a,Integer} (((number`{'n,Integer}) -`{Integer} i) -`{Integer} (1 :: Integer))))"

cryptol_definition rotate_r_l_neg :: "{'n,'a} ((fin 'n,Eq 'a,Zero 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"rotate_r_l_neg xs i \<equiv> (xs >>>`{'n,Integer,'a} i) ==`{['n]'a} (xs <<<`{'n,Integer,'a} (negate`{Integer} i))"

cryptol_definition rotatel_as_map :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"rotatel_as_map xs i \<equiv> (xs <<<`{'n,Integer,'a} i) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (xs @`{'n,'a,Integer} ((ix +`{Integer} i) %`{Integer} (number`{'n,Integer})))) (fromToLessThan`{0,'n,Integer}))"

cryptol_definition rotater_as_map :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"rotater_as_map xs i \<equiv> (xs >>>`{'n,Integer,'a} i) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (xs @`{'n,'a,Integer} ((ix -`{Integer} i) %`{Integer} (number`{'n,Integer})))) (fromToLessThan`{0,'n,Integer}))"

cryptol_definition scanl_valid :: "{'n,'k,'a,'b} ((fin 'n,'k < 'n,Eq 'b) =?> (('b \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> ((['n]'a) \<Rightarrow> Bit))))" where
"scanl_valid f x xs \<equiv> 
  let
    xs' = ((scanl`{'k,'b,'a} f x (take`{'k,'n - 'k,'a} xs)) : ([1 + 'k]'b))
  in ((scanl`{'n,'b,'a} f x xs) ==`{[1 + 'n]'b} ((butlast`{'k,'b} xs') #`{'k,1 + ('n - 'k),'b} (scanl`{'n - 'k,'b,'a} f (last`{'k,'b} xs') (drop`{'k,'n - 'k,'a} xs))))"

cryptol_definition scanr_valid :: "{'n,'k,'a,'b} ((fin 'n,'k < 'n,Eq 'b) =?> (('a \<Rightarrow> ('b \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> ((['n]'a) \<Rightarrow> Bit))))" where
"scanr_valid f x xs \<equiv> 
  let
    xs' = ((scanr`{'n - 'k,'a,'b} f x (drop`{'k,'n - 'k,'a} xs)) : ([1 + ('n - 'k)]'b))
  in ((scanr`{'n,'a,'b} f x xs) ==`{[1 + 'n]'b} ((butlast`{'k,'b} (scanr`{'k,'a,'b} f (head`{'n - 'k,'b} xs') (take`{'k,'n - 'k,'a} xs))) #`{'k,1 + ('n - 'k),'b} xs'))"

cryptol_definition selects_as_map :: "{'n,'k,'a} ((fin 'n,fin 'k,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['k]Integer) \<Rightarrow> Bit)))" where
"selects_as_map xs ixs \<equiv> (all`{'k,Integer} (\<lambda>(ix :: Integer). ((ix >=`{Integer} (0 :: Integer)) \<and> (ix <`{Integer} (number`{'n,Integer})))) ixs) \<longrightarrow> ((xs @@`{'n,'k,Integer,'a} ixs) ==`{['k]'a} (map`{'k,Integer,'a} (\<lambda>(ix :: Integer). (xs @`{'n,'a,Integer} ix)) ixs))"

cryptol_definition selects_end_as_map :: "{'n,'k,'a} ((fin 'n,fin 'k,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['k]Integer) \<Rightarrow> Bit)))" where
"selects_end_as_map xs ixs \<equiv> (all`{'k,Integer} (\<lambda>(ix :: Integer). ((ix >=`{Integer} (0 :: Integer)) \<and> (ix <`{Integer} (number`{'n,Integer})))) ixs) \<longrightarrow> ((xs !!`{'n,'k,Integer,'a} ixs) ==`{['k]'a} (map`{'k,Integer,'a} (\<lambda>(ix :: Integer). (xs !`{'n,'a,Integer} ix)) ixs))"

cryptol_definition shift_r_l_neg :: "{'n,'a} ((fin 'n,Eq 'a,Zero 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"shift_r_l_neg xs i \<equiv> (xs >>`{'n,Integer,'a} i) ==`{['n]'a} (xs <<`{'n,Integer,'a} (negate`{Integer} i))"

cryptol_definition shiftl_as_map :: "{'n,'a} ((fin 'n,Eq 'a,Zero 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"shiftl_as_map xs i \<equiv> (i >=`{Integer} (0 :: Integer)) \<longrightarrow> ((xs <<`{'n,Integer,'a} i) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (if (ix +`{Integer} i) <`{Integer} (number`{'n,Integer}) then (xs @`{'n,'a,Integer} (ix +`{Integer} i)) else coerce (zero`{'a}))) (fromToLessThan`{0,'n,Integer})))"

cryptol_definition shiftr_as_map :: "{'n,'a} ((fin 'n,Eq 'a,Zero 'a) =?> ((['n]'a) \<Rightarrow> (Integer \<Rightarrow> Bit)))" where
"shiftr_as_map xs i \<equiv> (i >=`{Integer} (0 :: Integer)) \<longrightarrow> ((xs >>`{'n,Integer,'a} i) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (if i <=`{Integer} ix then (xs @`{'n,'a,Integer} (ix -`{Integer} i)) else coerce (zero`{'a}))) (fromToLessThan`{0,'n,Integer})))"

cryptol_definition split_groupBy :: "{'parts,'each,'a} ((fin 'each,fin 'parts,Eq 'a) =?> ((['parts * 'each]'a) \<Rightarrow> Bit))" where
"split_groupBy x \<equiv> (groupBy`{'each,'parts,'a} x) ==`{['parts]['each]'a} (split`{'parts,'each,'a} x)"

cryptol_definition split_join :: "{'parts,'each,'a} ((fin 'each,fin 'parts,Eq 'a) =?> ((['parts * 'each]'a) \<Rightarrow> Bit))" where
"split_join x \<equiv> (join`{'parts,'each,'a} (split`{'parts,'each,'a} x)) ==`{['parts * 'each]'a} x"

cryptol_definition sum_as_fold :: "{'n,'a} ((fin 'n,Eq 'a,Ring 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"sum_as_fold xs \<equiv> (sum`{'n,'a} xs) ==`{'a} (foldl`{'n,'a,'a} (\<lblot>+`{'a}\<rblot>) (zero`{'a}) xs)"

cryptol_definition tail_is_drop :: "{'n,'a} (('n > 0,fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"tail_is_drop x \<equiv> (tail`{'n - 1,'a} x) ==`{['n - 1]'a} (drop`{1,'n - 1,'a} x)"

cryptol_definition take_append :: "{'front,'back,'a} ((fin 'front,Eq 'a) =?> ((['front]'a) \<Rightarrow> ((['back]'a) \<Rightarrow> Bit)))" where
"take_append x y \<equiv> (take`{'front,'back,'a} (x #`{'front,'back,'a} y)) ==`{['front]'a} x"

cryptol_definition take_drop_append :: "{'n,'m,'a} (('n \<ge> 'm,fin 'n,fin 'm,Eq 'a) =?> ((['n]'a) \<Rightarrow> Bit))" where
"take_drop_append x \<equiv> ((take`{'m,'n - 'm,'a} x) #`{'m,'n - 'm,'a} (drop`{'m,'n - 'm,'a} x)) ==`{['n]'a} x"

cryptol_definition transpose_rectangle :: "{'rows,'cols,'a} ((fin 'rows,fin 'cols,Eq 'a) =?> ((['rows]['cols]'a) \<Rightarrow> Bit))" where
"transpose_rectangle x \<equiv> (transpose`{'rows,'cols,'a} x) ==`{['cols]['rows]'a} (map`{'cols,Integer,['rows]'a} (\<lambda>(i :: Integer). (map`{'rows,Integer,'a} (\<lambda>(j :: Integer). ((x @`{'rows,['cols]'a,Integer} j) @`{'cols,'a,Integer} i)) (fromToLessThan`{0,'rows,Integer}))) (fromToLessThan`{0,'cols,Integer}))"

cryptol_definition update_as_map :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> ('a \<Rightarrow> (Integer \<Rightarrow> Bit))))" where
"update_as_map xs x i \<equiv> ((0 :: Integer) <=`{Integer} i) \<longrightarrow> ((i <`{Integer} (number`{'n,Integer})) \<longrightarrow> ((update`{'n,'a,Integer} xs i x) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (if ix ==`{Integer} i then x else coerce (xs @`{'n,'a,Integer} ix))) (fromToLessThan`{0,'n,Integer}))))"

cryptol_definition update_end_as_map :: "{'n,'a} ((fin 'n,Eq 'a) =?> ((['n]'a) \<Rightarrow> ('a \<Rightarrow> (Integer \<Rightarrow> Bit))))" where
"update_end_as_map xs x i \<equiv> ((0 :: Integer) <=`{Integer} i) \<longrightarrow> ((i <`{Integer} (number`{'n,Integer})) \<longrightarrow> ((updateEnd`{'n,'a,Integer} xs i x) ==`{['n]'a} (map`{'n,Integer,'a} (\<lambda>(ix :: Integer). (if ix ==`{Integer} (((number`{'n,Integer}) -`{Integer} i) -`{Integer} (1 :: Integer)) then x else coerce (xs @`{'n,'a,Integer} ix))) (fromToLessThan`{0,'n,Integer}))))"

cryptol_definition updatesEnd_as_foldl :: "{'n,'k,'a} ((fin 'n,fin 'k,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['k]'a) \<Rightarrow> ((['k]Integer) \<Rightarrow> Bit))))" where
"updatesEnd_as_foldl xs ys ixs \<equiv> (all`{'k,Integer} (\<lambda>(ix :: Integer). ((ix >=`{Integer} (0 :: Integer)) \<and> (ix <`{Integer} (number`{'n,Integer})))) ixs) \<longrightarrow> ((updatesEnd`{'n,'k,Integer,'a} xs ixs ys) ==`{['n]'a} (foldl`{'k,['n]'a,('a) \<times> (Integer)} (\<lambda>(xs' :: ['n]'a) (i__p1 :: ('a) \<times> (Integer)). (
  let
      ix = ((\<lambda>(_,x). x) i__p1 :: Integer);
    y = ((\<lambda>(x,_). x) i__p1 :: 'a)
  in (updateEnd`{'n,'a,Integer} xs' ix y))) xs (zip`{'k,'a,Integer} ys ixs)))"

cryptol_definition updates_as_foldl :: "{'n,'k,'a} ((fin 'n,fin 'k,Eq 'a) =?> ((['n]'a) \<Rightarrow> ((['k]'a) \<Rightarrow> ((['k]Integer) \<Rightarrow> Bit))))" where
"updates_as_foldl xs ys ixs \<equiv> (all`{'k,Integer} (\<lambda>(ix :: Integer). ((ix >=`{Integer} (0 :: Integer)) \<and> (ix <`{Integer} (number`{'n,Integer})))) ixs) \<longrightarrow> ((updates`{'n,'k,Integer,'a} xs ixs ys) ==`{['n]'a} (foldl`{'k,['n]'a,('a) \<times> (Integer)} (\<lambda>(xs' :: ['n]'a) (i__p0 :: ('a) \<times> (Integer)). (
  let
      ix = ((\<lambda>(_,x). x) i__p0 :: Integer);
    y = ((\<lambda>(x,_). x) i__p0 :: 'a)
  in (update`{'n,'a,Integer} xs' ix y))) xs (zip`{'k,'a,Integer} ys ixs)))"

cryptol_definition zipWith_as_map :: "{'n,'a,'b,'c} ((fin 'n,Eq 'c) =?> (('a \<Rightarrow> ('b \<Rightarrow> 'c)) \<Rightarrow> ((['n]'a) \<Rightarrow> ((['n]'b) \<Rightarrow> Bit))))" where
"zipWith_as_map f xs ys \<equiv> (zipWith`{'n,'a,'b,'c} f xs ys) ==`{['n]'c} (map`{'n,Integer,'c} (\<lambda>(ix :: Integer). (f`{} (xs @`{'n,'a,Integer} ix) (ys @`{'n,'b,Integer} ix))) (fromToLessThan`{0,'n,Integer}))"

cryptol_definition zip_as_map :: "{'n,'a,'b} ((fin 'n,Eq 'a,Eq 'b) =?> ((['n]'a) \<Rightarrow> ((['n]'b) \<Rightarrow> Bit)))" where
"zip_as_map xs ys \<equiv> (zip`{'n,'a,'b} xs ys) ==`{['n](('a) \<times> ('b))} (map`{'n,Integer,('a) \<times> ('b)} (\<lambda>(ix :: Integer). ((xs @`{'n,'a,Integer} ix,ys @`{'n,'b,Integer} ix))) (fromToLessThan`{0,'n,Integer}))"

end
end
