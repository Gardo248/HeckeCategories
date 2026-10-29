#############################################################
# test.g -- test per coxeter.g
#
# Uso (dalla directory dei file):   gap -q test.g
# oppure da GAP:                    Read("test.g");
#############################################################

Read("coxeter.g");

TEST_COUNT := 0;
TEST_FAILED := 0;

# Confronta il valore ottenuto con quello atteso
CheckEqual := function(name, got, expected)
  TEST_COUNT := TEST_COUNT + 1;
  if got <> expected then
    TEST_FAILED := TEST_FAILED + 1;
    Print("FAIL: ", name, "\n   atteso: ", expected, "\n   ottenuto: ", got, "\n");
  fi;
end;

# Verifica che la chiamata f(args) generi un errore
CheckError := function(name, f, args)
  local res, old;
  TEST_COUNT := TEST_COUNT + 1;
  # senza questo, Error() entra nel break loop invece di essere catturato
  old := BreakOnError;
  BreakOnError := false;
  res := CALL_WITH_CATCH(f, args);
  BreakOnError := old;
  if res[1] = true then
    TEST_FAILED := TEST_FAILED + 1;
    Print("FAIL: ", name, " (era atteso un errore)\n");
  fi;
end;

# ---- generatori di matrici di Coxeter -----------------------
# Diagramma a catena di lunghezza n, con etichette `labels`
# (m_{i,i+1} = labels[i]); le altre coppie hanno m = 2.
ChainMatrix := function(n, labels)
  local M, i;
  M := List([1..n], i -> List([1..n], j -> 2));
  for i in [1..n] do M[i][i] := 1; od;
  for i in [1..n-1] do
    M[i][i+1] := labels[i];
    M[i+1][i] := labels[i];
  od;
  return M;
end;

# Matrice a partire da una lista di archi [i,j,m] (m=3 se omesso)
GraphMatrix := function(n, edges)
  local M, e;
  M := List([1..n], i -> List([1..n], j -> 2));
  for e in [1..n] do M[e][e] := 1; od;
  for e in edges do
    M[e[1]][e[2]] := e[3];
    M[e[2]][e[1]] := e[3];
  od;
  return M;
end;

#############################################################
# 1. Struttura dell'oggetto
#############################################################
G := CoxeterGroupByMatrix([[1,3],[3,1]], ["s","t"]);
CheckEqual("IsCoxeterGroup", IsCoxeterGroup(G), true);
CheckEqual("IsGroup", IsGroup(G), true);
CheckEqual("CoxeterMatrix", CoxeterMatrix(G), [[1,3],[3,1]]);
CheckEqual("CoxeterGeneratorNames", CoxeterGeneratorNames(G), ["s","t"]);
CheckEqual("numero generatori", Length(GeneratorsOfGroup(G)), 2);

G := CoxeterGroupByMatrix([[1,3,2],[3,1,3],[2,3,1]]);
CheckEqual("nomi di default", CoxeterGeneratorNames(G), ["s1","s2","s3"]);

#############################################################
# 2. Relazioni
#############################################################
G := CoxeterGroupByMatrix(ChainMatrix(3, [3,4]));   # B3
CheckEqual("s^2 = e", ForAll(GeneratorsOfGroup(G), s -> s^2 = One(G)), true);
CheckEqual("(s1 s2)^3 = e",
  (GeneratorsOfGroup(G)[1]*GeneratorsOfGroup(G)[2])^3 = One(G), true);
CheckEqual("(s2 s3)^4 = e",
  (GeneratorsOfGroup(G)[2]*GeneratorsOfGroup(G)[3])^4 = One(G), true);
CheckEqual("(s1 s3)^2 = e",
  (GeneratorsOfGroup(G)[1]*GeneratorsOfGroup(G)[3])^2 = One(G), true);
CheckEqual("(s1 s2)^2 <> e",
  (GeneratorsOfGroup(G)[1]*GeneratorsOfGroup(G)[2])^2 = One(G), false);

#############################################################
# 3. Ordini di gruppi finiti noti
#############################################################
CheckEqual("rango 0",  Size(CoxeterGroupByMatrix([])), 1);
CheckEqual("A1",       Size(CoxeterGroupByMatrix([[1]])), 2);
CheckEqual("A1xA1",    Size(CoxeterGroupByMatrix([[1,2],[2,1]])), 4);
CheckEqual("A2",       Size(CoxeterGroupByMatrix(ChainMatrix(2,[3]))), 6);
CheckEqual("A3",       Size(CoxeterGroupByMatrix(ChainMatrix(3,[3,3]))), 24);
CheckEqual("A4",       Size(CoxeterGroupByMatrix(ChainMatrix(4,[3,3,3]))), 120);
CheckEqual("A5",       Size(CoxeterGroupByMatrix(ChainMatrix(5,[3,3,3,3]))), 720);
CheckEqual("B2=I2(4)", Size(CoxeterGroupByMatrix(ChainMatrix(2,[4]))), 8);
CheckEqual("B3",       Size(CoxeterGroupByMatrix(ChainMatrix(3,[3,4]))), 48);
CheckEqual("B4",       Size(CoxeterGroupByMatrix(ChainMatrix(4,[3,3,4]))), 384);
CheckEqual("G2=I2(6)", Size(CoxeterGroupByMatrix(ChainMatrix(2,[6]))), 12);
CheckEqual("I2(5)",    Size(CoxeterGroupByMatrix(ChainMatrix(2,[5]))), 10);
CheckEqual("I2(7)",    Size(CoxeterGroupByMatrix(ChainMatrix(2,[7]))), 14);
CheckEqual("H3",       Size(CoxeterGroupByMatrix(ChainMatrix(3,[5,3]))), 120);
CheckEqual("H4",       Size(CoxeterGroupByMatrix(ChainMatrix(4,[5,3,3]))), 14400);
CheckEqual("F4",       Size(CoxeterGroupByMatrix(ChainMatrix(4,[3,4,3]))), 1152);
# D4: nodo 2 al centro, collegato a 1, 3, 4
CheckEqual("D4",
  Size(CoxeterGroupByMatrix(GraphMatrix(4, [[1,2,3],[2,3,3],[2,4,3]]))), 192);
# E6, E7, E8 (numerazione di Bourbaki)
CheckEqual("E6",
  Size(CoxeterGroupByMatrix(GraphMatrix(6,
    [[1,3,3],[3,4,3],[4,5,3],[5,6,3],[2,4,3]]))), 51840);
CheckEqual("E7",
  Size(CoxeterGroupByMatrix(GraphMatrix(7,
    [[1,3,3],[3,4,3],[4,5,3],[5,6,3],[6,7,3],[2,4,3]]))), 2903040);
CheckEqual("E8",
  Size(CoxeterGroupByMatrix(GraphMatrix(8,
    [[1,3,3],[3,4,3],[4,5,3],[5,6,3],[6,7,3],[7,8,3],[2,4,3]]))), 696729600);

#############################################################
# 4. Gruppi infiniti
#############################################################
D := CoxeterGroupByMatrix([[1,infinity],[infinity,1]]);
CheckEqual("D_inf Size",     Size(D), infinity);
CheckEqual("D_inf IsFinite", IsFinite(D), false);
CheckEqual("D_inf gens",     Length(GeneratorsOfGroup(D)), 2);

A2t := CoxeterGroupByMatrix(GraphMatrix(3, [[1,2,3],[2,3,3],[1,3,3]]));
CheckEqual("A2 affine Size", Size(A2t), infinity);
CheckEqual("B2 affine (4,4,2)",
  IsFinite(CoxeterGroupByMatrix(GraphMatrix(3,[[1,2,4],[2,3,4]]))), false);
CheckEqual("iperbolico (3,3,7)",
  IsFinite(CoxeterGroupByMatrix(GraphMatrix(3,[[1,2,3],[2,3,3],[1,3,7]]))),
  false);
CheckEqual("D4 affine",
  IsFinite(CoxeterGroupByMatrix(
    GraphMatrix(5,[[1,3,3],[2,3,3],[3,4,3],[3,5,3]]))), false);

#############################################################
# 5. Test sulla matrice (senza costruire il gruppo)
#############################################################
CheckEqual("IsFiniteCoxeterMatrix A3",
  IsFiniteCoxeterMatrix(ChainMatrix(3,[3,3])), true);
CheckEqual("IsFiniteCoxeterMatrix affine",
  IsFiniteCoxeterMatrix(GraphMatrix(3,[[1,2,3],[2,3,3],[1,3,3]])), false);

#############################################################
# 5b. Forma bilineare (attributo del gruppo)
#############################################################
CheckEqual("forma bilineare A2",
  CoxeterBilinearForm(CoxeterGroupByMatrix(ChainMatrix(2,[3]))),
  [[1,-1/2],[-1/2,1]]);
CheckEqual("forma bilineare con infinity",
  CoxeterBilinearForm(CoxeterGroupByMatrix([[1,infinity],[infinity,1]])),
  [[1,-1],[-1,1]]);
CheckEqual("forma bilineare m=2 (ortogonali)",
  CoxeterBilinearForm(CoxeterGroupByMatrix([[1,2],[2,1]])), [[1,0],[0,1]]);

#############################################################
# 6. Rappresentazione di riflessioni
#############################################################
G := CoxeterGroupByMatrix(ChainMatrix(3,[3,3]));
rho := CoxeterReflectionRepresentation(G);
CheckEqual("rho iniettiva (A3)", IsInjective(rho), true);
CheckEqual("rho |Im| (A3)", Size(Image(rho)), 24);
mats := CoxeterReflectionMatrices(G);
CheckEqual("riflessioni: ordine 2", ForAll(mats, A -> Order(A) = 2), true);
CheckEqual("riflessioni: det -1", ForAll(mats, A -> DeterminantMat(A) = -1), true);
CheckEqual("ordine s1 s2", Order(mats[1]*mats[2]), 3);
CheckEqual("ordine s1 s3", Order(mats[1]*mats[3]), 2);

# H3 (usa sqrt(5)): ordini dei prodotti
mats := CoxeterReflectionMatrices(CoxeterGroupByMatrix(ChainMatrix(3,[5,3])));
CheckEqual("H3 ordine s1 s2", Order(mats[1]*mats[2]), 5);
CheckEqual("H3 ordine s2 s3", Order(mats[2]*mats[3]), 3);
CheckEqual("H3 ordine s1 s3", Order(mats[1]*mats[3]), 2);

# la rappresentazione e' un omomorfismo (verifica sul prodotto)
G := CoxeterGroupByMatrix(ChainMatrix(3,[3,4]));
rho := CoxeterReflectionRepresentation(G);
g := GeneratorsOfGroup(G);
CheckEqual("rho e' omomorfismo",
  (g[1]*g[2]*g[3])^rho, g[1]^rho * g[2]^rho * g[3]^rho);

# gruppi infiniti: i generatori hanno la rappresentazione attesa
# (non si calcola IsInjective: non terminerebbe su un gruppo fp infinito)
D := CoxeterGroupByMatrix([[1,infinity],[infinity,1]]);
rho := CoxeterReflectionRepresentation(D);
CheckEqual("rho D_inf: s1 -> riflessione",
  GeneratorsOfGroup(D)[1]^rho, [[-1,0],[2,1]]);
CheckEqual("rho D_inf: s2 -> riflessione",
  GeneratorsOfGroup(D)[2]^rho, [[1,2],[0,-1]]);

#############################################################
# 7. Rappresentazione in permutazioni (solo gruppi finiti)
#############################################################
G := CoxeterGroupByMatrix(ChainMatrix(3,[3,3]));
pi := CoxeterPermutationRepresentation(G);
CheckEqual("pi iniettiva (A3)", IsInjective(pi), true);
CheckEqual("pi |Im| (A3)", Size(Image(pi)), 24);
CheckEqual("A3: 12 radici", LargestMovedPoint(Image(pi)), 12);

G := CoxeterGroupByMatrix(ChainMatrix(3,[5,3]));
CheckEqual("H3 pi iniettiva", IsInjective(CoxeterPermutationRepresentation(G)), true);
CheckEqual("H3: 30 radici",
  LargestMovedPoint(Image(CoxeterPermutationRepresentation(G))), 30);

Print("(le righe 'Error, ...' seguenti sono errori ATTESI, catturati dai test)\n");
CheckError("pi su gruppo infinito",
  CoxeterPermutationRepresentation, [D]);

#############################################################
# 8. Errori di validazione degli input
#############################################################
CheckError("non simmetrica",
  CoxeterGroupByMatrix, [[[1,3],[4,1]]]);
CheckError("diagonale <> 1",
  CoxeterGroupByMatrix, [[[2,3],[3,1]]]);
CheckError("entrata fuori diagonale = 1",
  CoxeterGroupByMatrix, [[[1,1],[1,1]]]);
CheckError("entrata fuori diagonale = 0",
  CoxeterGroupByMatrix, [[[1,0],[0,1]]]);
CheckError("entrata negativa",
  CoxeterGroupByMatrix, [[[1,-3],[-3,1]]]);
CheckError("entrata non intera",
  CoxeterGroupByMatrix, [[[1,5/2],[5/2,1]]]);
CheckError("matrice non quadrata",
  CoxeterGroupByMatrix, [[[1,3,2],[3,1,2]]]);
CheckError("nomi: numero sbagliato",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], ["s"]]);
CheckError("nomi: duplicati",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], ["s","s"]]);
CheckError("nomi: non stringhe",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], [1,2]]);

#############################################################
# Riepilogo
#############################################################
Print("\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " test superati");
if TEST_FAILED = 0 then
  Print(" -- TUTTO OK\n");
else
  Print(" -- ", TEST_FAILED, " FALLITI\n");
fi;
