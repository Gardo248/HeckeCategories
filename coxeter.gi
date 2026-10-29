#############################################################
# coxeter.gi -- IMPLEMENTAZIONI
#############################################################

#############################################################
# Forma bilineare e riflessioni (attributi del gruppo)
#############################################################

#TUTTO VA CONTROLLATO!!!!!!!!!!!!!!!!!!!!!!!

# Forma bilineare B(e_i,e_j) = -cos(pi/m_ij), in forma esatta
# (numeri ciclotomici). Se m_ij = infinity si pone B = -1.
InstallMethod(CoxeterBilinearForm, "for a Coxeter group",
  [IsCoxeterGroup],
function(G)
  local M, n, B, i, j, m;
  M := CoxeterMatrix(G);
  n := Length(M);
  B := List([1..n], i -> List([1..n], j -> 0));
  for i in [1..n] do
    for j in [1..n] do
      m := M[i][j];
      if m = infinity then
        B[i][j] := -1;
      else
        B[i][j] := -(E(2*m) + E(2*m)^-1) / 2;   # = -cos(pi/m)
      fi;
    od;
  od;
  return B;
end);

# Matrici (azione a destra sui vettori riga) delle riflessioni
#   s_i : v -> v - 2 B(e_i, v) e_i
# La riga j dell'i-esima matrice e' l'immagine di e_j.
InstallMethod(CoxeterReflectionMatrices, "for a Coxeter group",
  [IsCoxeterGroup],
function(G)
  local n, B, mats, i, j, A;
  B := CoxeterBilinearForm(G);
  n := Length(B);
  mats := [];
  for i in [1..n] do
    A := IdentityMat(n);
    for j in [1..n] do
      A[j][i] := A[j][i] - 2*B[i][j];
    od;
    Add(mats, A);
  od;
  return mats;
end);

#############################################################
# Funzioni sulla matrice di Coxeter
#############################################################

# Un gruppo di Coxeter e' finito se e solo se la forma B e'
# definita positiva. Test numerico (eliminazione gaussiana in
# virgola mobile): i pivot devono essere tutti > eps.
InstallGlobalFunction(IsFiniteCoxeterMatrix, function(M)
  local n, B, i, j, k, f, m, eps;
  n := Length(M);
  eps := Float(1) / Float(10^12);
  B := List([1..n], i -> List([1..n], j -> Float(0)));
  for i in [1..n] do
    for j in [1..n] do
      m := M[i][j];
      if m = infinity then
        B[i][j] := -Float(1);
      else
        B[i][j] := -Cos(FLOAT.PI / Float(m));
      fi;
    od;
  od;
  for k in [1..n] do
    if B[k][k] <= eps then
      return false;
    fi;
    for i in [k+1..n] do
      f := B[i][k] / B[k][k];
      for j in [k..n] do
        B[i][j] := B[i][j] - f * B[k][j];
      od;
    od;
  od;
  return true;
end);

#############################################################
# Costruzione del gruppo
#############################################################

InstallMethod(CoxeterGroupByMatrix, "with generator names",
  [IsList, IsList],
function(M, names)
  local n, i, j, m, F, gens, rels, G;

  n := Length(M);

  # --- controllo dei nomi ---
  if Length(names) <> n or not ForAll(names, IsString) then
    Error("names must be a list of ", n, " strings");
  fi;
  if not IsDuplicateFreeList(names) then
    Error("names must be distinct");
  fi;

  # --- controllo della matrice ---
  if not ForAll(M, r -> IsList(r) and Length(r) = n) then
    Error("M must be a square matrix of size ", n);
  fi;
  for i in [1..n] do
    if M[i][i] <> 1 then
      Error("diagonal entries must be 1");
    fi;
    for j in [1..i-1] do
      if M[i][j] <> M[j][i] then
        Error("matrix must be symmetric");
      fi;
      m := M[i][j];
      if not (m = infinity or (IsPosInt(m) and m >= 2)) then
        Error("off-diagonal entries must be integers >= 2 or infinity");
      fi;
    od;
  od;

  # --- gruppo libero e relazioni ---
  if n = 0 then
    G := FreeGroup(0) / [];
  else
    F    := FreeGroup(names);
    gens := GeneratorsOfGroup(F);
    rels := [];
    for i in [1..n] do
      Add(rels, (gens[i]*gens[i])^M[i][i]);          # s_i^2
      for j in [i+1..n] do
        if M[i][j] <> infinity then
          Add(rels, (gens[i]*gens[j])^M[i][j]);      # (s_i s_j)^m_ij
        fi;
      od;
    od;
    G := F / rels;
  fi;

  SetFilterObj(G, IsCoxeterGroup);
  SetCoxeterMatrix(G, M);
  SetCoxeterGeneratorNames(G, names);
  return G;
end);

InstallMethod(CoxeterGroupByMatrix, "default names",
  [IsList],
M -> CoxeterGroupByMatrix(M,
         List([1..Length(M)], i -> Concatenation("s", String(i)))));

#############################################################
# Rappresentazioni
#############################################################

InstallMethod(CoxeterReflectionRepresentation, "for a Coxeter group",
  [IsCoxeterGroup],
function(G)
  local mats, H;
  if Length(CoxeterMatrix(G)) = 0 then
    Error("rank 0: no reflection representation");
  fi;
  mats := CoxeterReflectionMatrices(G);
  H := Group(mats);
  # Per il teorema di Tits le matrici soddisfano le relazioni e la
  # rappresentazione e' fedele: si puo' usare la versione NC.
  return GroupHomomorphismByImagesNC(G, H, GeneratorsOfGroup(G), mats);
end);

InstallMethod(CoxeterPermutationRepresentation, "for a Coxeter group",
  [IsCoxeterGroup],
function(G)
  local M, n, mats, H, roots, perms, P;
  M := CoxeterMatrix(G);
  n := Length(M);
  if n = 0 then
    Error("rank 0: no permutation representation");
  fi;
  if not IsFiniteCoxeterMatrix(M) then
    Error("the Coxeter group is infinite");
  fi;
  mats  := CoxeterReflectionMatrices(G);
  H     := Group(mats);
  # insieme delle radici = unione delle orbite dei vettori e_i
  roots := Set(Concatenation(
             List(IdentityMat(n), v -> Orbit(H, v, OnRight))));
  perms := List(mats,
             A -> PermList(List(roots, r -> Position(roots, r*A))));
  P := Group(perms);
  return GroupHomomorphismByImagesNC(G, P, GeneratorsOfGroup(G), perms);
end);

#############################################################
# Metodi veloci (evitano l'enumerazione dei laterali sul gruppo fp)
#############################################################

InstallMethod(IsFinite, "for a Coxeter group",
  [IsCoxeterGroup and IsFpGroup], SUM_FLAGS,
  G -> Length(CoxeterMatrix(G)) = 0
       or IsFiniteCoxeterMatrix(CoxeterMatrix(G)));

InstallMethod(Size, "for a Coxeter group",
  [IsCoxeterGroup and IsFpGroup], SUM_FLAGS,
function(G)
  if Length(CoxeterMatrix(G)) = 0 then
    return 1;
  elif not IsFiniteCoxeterMatrix(CoxeterMatrix(G)) then
    return infinity;
  fi;
  return Size(Image(CoxeterPermutationRepresentation(G)));
end);
