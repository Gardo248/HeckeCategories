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

# Forma bilineare di Coxeter (esatta) e matrici delle riflessioni
# semplici nella rappresentazione geometrica: calcolate una sola
# volta per gruppo (valori immutabili).
DeclareAttribute("CoxeterBilinearForm", IsCoxeterGroup);
DeclareAttribute("CoxeterReflectionMatrices", IsCoxeterGroup);

# Funzioni che lavorano sulla sola matrice di Coxeter M
DeclareGlobalFunction("IsFiniteCoxeterMatrix");
