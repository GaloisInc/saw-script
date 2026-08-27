theory "Nested"
imports "Cryptol.Cryptol" Qualifier1_Qualified Qualifier2_Qualified
begin

context includes cryptol_translation_syntax begin
type_synonym ('n) Q2R = "('n) Qualifier2_Qualified.R"

end
end
