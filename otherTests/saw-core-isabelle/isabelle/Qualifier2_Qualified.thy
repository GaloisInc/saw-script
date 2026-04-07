theory "Qualifier2_Qualified"
imports "Cryptol.Cryptol" RecordDecls
begin

context includes cryptol_translation_syntax begin
type_synonym ('n) R = "('n) RecordDecls.R"

end
end
