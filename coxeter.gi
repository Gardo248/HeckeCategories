#############################################################
# coxeter.gi -- IMPLEMENTATIONS
#############################################################

#############################################################
# Bilinear form and reflections (attributes of the group)
#############################################################

#EVERYTHING MUST BE CHECKED!!!!!!!!!!!!!!!!!!!!!!!

# Bilinear form B(e_i,e_j) = -cos(pi/m_ij), in exact form
# (cyclotomic numbers). If m_ij = infinity we set B = -1.
InstallMethod(CoxeterBilinearForm, "for a Coxeter group",
  [IsCoxeterGroup],
function(W)
  local M, n, B, i, j, m;
  M := CoxeterMatrix(W);
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

# Matrices (right action on row vectors) of the reflections
#   s_i : v -> v - 2 B(e_i, v) e_i
# Row j of the i-th matrix is the image of e_j.
InstallMethod(CoxeterReflectionMatrices, "for a Coxeter group",
  [IsCoxeterGroup],
function(W)
  local n, B, mats, i, j, A;
  B := CoxeterBilinearForm(W);
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
# Functions on the Coxeter matrix
#############################################################

# A Coxeter group is finite if and only if the form B is
# positive definite. Numerical test (floating point Gaussian
# elimination): the pivots must all be > eps.
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
# Construction of the group
#############################################################

InstallMethod(CoxeterGroupByMatrix, "with generator names",
  [IsList, IsList],
function(M, names)
  local n, i, j, m, F, gens, rels, W;

  n := Length(M);

  # --- check of the names ---
  if Length(names) <> n or not ForAll(names, IsString) then
    Error("names must be a list of ", n, " strings");
  fi;
  if not IsDuplicateFreeList(names) then
    Error("names must be distinct");
  fi;

  # --- check of the matrix ---
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

  # --- free group and relations ---
  if n = 0 then
    W := FreeGroup(0) / [];
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
    W := F / rels;
  fi;

  SetFilterObj(W, IsCoxeterGroup);
  SetCoxeterMatrix(W, M);
  SetCoxeterGeneratorNames(W, names);
  return W;
end);

InstallMethod(CoxeterGroupByMatrix, "default names",
  [IsList],
M -> CoxeterGroupByMatrix(M,
         List([1..Length(M)], i -> Concatenation("s", String(i)))));

#############################################################
# Representations
#############################################################

InstallMethod(CoxeterReflectionRepresentation, "for a Coxeter group",
  [IsCoxeterGroup],
function(W)
  local mats, H;
  if Length(CoxeterMatrix(W)) = 0 then
    Error("rank 0: no reflection representation");
  fi;
  mats := CoxeterReflectionMatrices(W);
  H := Group(mats);
  # By Tits' theorem the matrices satisfy the relations and the
  # representation is faithful: the NC version can be used.
  return GroupHomomorphismByImagesNC(W, H, GeneratorsOfGroup(W), mats);
end);

InstallMethod(CoxeterPermutationRepresentation, "for a Coxeter group",
  [IsCoxeterGroup],
function(W)
  local M, n, mats, H, roots, perms, P;
  M := CoxeterMatrix(W);
  n := Length(M);
  if n = 0 then
    Error("rank 0: no permutation representation");
  fi;
  if not IsFiniteCoxeterMatrix(M) then
    Error("the Coxeter group is infinite");
  fi;
  mats  := CoxeterReflectionMatrices(W);
  H     := Group(mats);
  # set of roots = union of the orbits of the vectors e_i
  roots := Set(Concatenation(
             List(IdentityMat(n), v -> Orbit(H, v, OnRight))));
  perms := List(mats,
             A -> PermList(List(roots, r -> Position(roots, r*A))));
  P := Group(perms);
  return GroupHomomorphismByImagesNC(W, P, GeneratorsOfGroup(W), perms);
end);

#############################################################
# Fast methods (avoid coset enumeration on the fp group)
#############################################################

InstallMethod(IsFinite, "for a Coxeter group",
  [IsCoxeterGroup and IsFpGroup], SUM_FLAGS,
  W -> Length(CoxeterMatrix(W)) = 0
       or IsFiniteCoxeterMatrix(CoxeterMatrix(W)));

InstallMethod(Size, "for a Coxeter group",
  [IsCoxeterGroup and IsFpGroup], SUM_FLAGS,
function(W)
  if Length(CoxeterMatrix(W)) = 0 then
    return 1;
  elif not IsFiniteCoxeterMatrix(CoxeterMatrix(W)) then
    return infinity;
  fi;
  return Size(Image(CoxeterPermutationRepresentation(W)));
end);
