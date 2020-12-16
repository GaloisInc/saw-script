enable_experimental;
a <- java_load_class "Arr";

print "**Extracting main";
main <- java_extract j "main";


print "**Evaluating: single array ref";
sat_print abc {{ \(x:[32]) -> main 0 == x }};

print "Done.";
