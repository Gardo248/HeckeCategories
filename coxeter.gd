#############################################################
# coxeter.gd -- DICHIARAZIONI
#############################################################

DeclareCategory("IsCoxeterGroup", IsGroup);

DeclareAttribute("CoxeterMatrix", IsGroup);
DeclareAttribute("CoxeterGeneratorNames", IsGroup);

# Omomorfismo fedele G -> gruppo di matrici generato dalle riflessioni
# (rappresentazione geometrica di Tits). Vale per ogni gruppo di Coxeter.
DeclareAttribute("CoxeterReflectionRepresentation", IsCoxeterGroup);

# Omomorfismo fedele G -> gruppo di permutazioni sulle radici.
# Esiste solo se il gruppo e' finito.
DeclareAttribute("CoxeterPermutationRepresentation", IsCoxeterGroup);

# Costruttori. La matrice e' IsList e non IsMatrix: con entrate
# `infinity` il filtro IsMatrix potrebbe non essere soddisfatto.
DeclareOperation("CoxeterGroupByMatrix", [IsList]);
DeclareOperation("CoxeterGroupByMatrix", [IsList, IsList]);

# Funzioni che lavorano sulla sola matrice di Coxeter M
DeclareGlobalFunction("CoxeterBilinearForm");
DeclareGlobalFunction("CoxeterReflectionMatrices");
DeclareGlobalFunction("IsFiniteCoxeterMatrix");
