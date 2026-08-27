theory Unsupported
imports Main Type_Predicate Coercible "HOL-Library.Type_Length" Integral "HOL-Library.Word"
begin

datatype 'a unsupportedT = unsupportedTTypeCtr


axiomatization 
  where unsupported: "\<And>P. PROP P"

instantiation unsupportedT :: (_) len begin
instance by (rule unsupported)
end


instantiation unsupportedT :: (_) linordered_euclidean_semiring_bit_operations begin
instance by (rule unsupported)
end


instantiation unsupportedT :: (_) integral begin
instance by (rule unsupported)
end

instantiation unsupportedT :: (_) pred begin
instance by (rule unsupported)
end

instantiation unsupportedT :: (_) coercible_atom begin
instance by (rule unsupported)
end

instantiation unsupportedT :: (_) finite begin
instance by (rule unsupported)
end

hide_fact unsupported
end