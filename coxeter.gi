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

#############################################################
# Combinatorics of words (inversion sets, normal forms,
# subexpressions)
#
# Mathematics (see the attached explanation):
#   B = Coxeter bilinear form, exact (CoxeterBilinearForm).
#   s_i acts on coordinate vectors v = sum_j v_j alpha_j as
#       s_i(v) = v - 2 B(alpha_i, v) alpha_i,
#   i.e. it changes only the i-th coordinate:
#       v_i  ->  v_i - 2 * sum_j B[i][j] * v_j.
#   I(w) = { beta > 0 : w(beta) < 0 }.  Facts (Tits, Humphreys 5.4-5.6):
#     (1) s_i is a right descent of w  <=>  alpha_i in I(w);
#     (2) if alpha_i in I(w):  I(w s_i) = s_i( I(w) \ {alpha_i} );
#         otherwise:           I(w s_i) = { alpha_i } u s_i( I(w) ).
#   No sign comparison: only equality between exact vectors.
#############################################################

# reflection s_i on the vector v (coordinates in the simple roots)
BindGlobal( "ReflectionInGeomRepr",
function( B, i, v )
  local sv;
  sv := ShallowCopy( v );
  sv[i] := v[i] - 2 * Sum( [ 1 .. Length( v ) ], j -> B[i][j] * v[j] );
  return sv;
end );

#TODO: I think this is superfluous, this check should be done in IsWellDefined
BindGlobal( "CheckCoxeterWord",
function( W, x )
  local n;
  n := Length( CoxeterMatrix( W ) );
  if not ForAll( x, i -> IsPosInt( i ) and i <= n ) then
    Error( "the word must be a list of integers in [1..", n, "]" );
  fi;
end );

##
InstallMethod( InversionSetAfterRightMultiplication,
  "for a Coxeter group, an inversion set and a generator index",
  [ IsCoxeterGroup, IsList, IsPosInt ],
function( W, I, i )
  local B, n, alpha, J;
  B := CoxeterBilinearForm( W );
  n := Length( B );
  alpha := List( [ 1 .. n ], j -> 0 );
  alpha[i] := 1;
  if alpha in I then
    J := List( Filtered( I, v -> v <> alpha ), v -> ReflectionInGeomRepr( B, i, v ) );
  else
    J := Concatenation( [ alpha ], List( I, v -> ReflectionInGeomRepr( B, i, v ) ) );
  fi;
  return Set( J );
end );

##
InstallMethod( InversionSetOfCoxeterWord,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
function( W, word )
  local I, i;
  CheckCoxeterWord( W, word );
  I := [ ];
  for i in word do
    I := InversionSetAfterRightMultiplication( W, I, i );
  od;
  return I;
end );

##
InstallMethod( CoxeterNormalFormOfInversionSet,
  "for a Coxeter group and an inversion set",
  [ IsCoxeterGroup, IsList ],
function( W, I )
  local n, alphas, word, i, found;
  n := Length( CoxeterMatrix( W ) );
  alphas := IdentityMat( n );
  word := [ ];
  while not IsEmpty( I ) do
    found := false;
    for i in [ 1 .. n ] do
      if alphas[i] in I then
        # s_i is the smallest right descent: w = w' s_i
        Add( word, i );
        I := InversionSetAfterRightMultiplication( W, I, i );
        found := true;
        break;
      fi;
    od;
    if not found then
      Error( "not a valid inversion set: no right descent found" );
      #TODO: ATTENTION this checks only that the set at every step contains a simple root, that does not guarantee that the set is actually an inversion set of some element of W. Maybe there will be more test about it
    fi;
  od;
  return Reversed( word );
end );

##
InstallMethod( CoxeterNormalFormOfWord,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
  { W, word } -> CoxeterNormalFormOfInversionSet( W,
                   InversionSetOfCoxeterWord( W, word ) ) );

##
#the function uses a recursion to find all the subexpressions of a word, and, step by step, it computes the inversion set of the subexpression.
#Then it computes the normal form of the inversion set, just once for each inversion set. To do that it uses a cache key,
#which contains all the inversion sets whose normal form has already been computed, and a cache value, which contains the normal forms of the inversion sets in the cache key.
#The function returns a list of pairs [e, w], where e is a 0/1 list representing the subexpression and w is the normal form of the inversion set of that subexpression.
InstallMethod( SubexpressionsOfCoxeterWord,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
function( W, x )
  local n, leaves, cache_keys, cache_vals, walk, res, leaf, p;
  CheckCoxeterWord( W, x );
  n := Length( x );
  leaves := [ ];                      # lists [ e, I ]
  walk := function( k, e, I )
    if k > n then
      Add( leaves, [ ShallowCopy( e ), I ] );
      return;
    fi;
    Add( e, 0 );
    walk( k + 1, e, I );
    Remove( e );
    Add( e, 1 );
    walk( k + 1, e, InversionSetAfterRightMultiplication( W, I, x[k] ) );
    Remove( e );
  end;
  walk( 1, [ ], [ ] );
  # the normal form is computed only once for each inversion set
  cache_keys := [ ];
  cache_vals := [ ];
  res := [ ];
  for leaf in leaves do
    p := Position( cache_keys, leaf[2] );
    if p = fail then
      Add( cache_keys, leaf[2] );
      Add( cache_vals, CoxeterNormalFormOfInversionSet( W, leaf[2] ) );
      p := Length( cache_keys );
    fi;
    Add( res, [ leaf[1], cache_vals[p] ] );
  od;
  return res;
end );

##
# Groups the subexpressions of x by endpoint: returns
# rec( endpoints, fibers ), with endpoints = distinct endpoints (sorted)
# and fibers[j] = subexpressions ending in endpoints[j].
InstallMethod( SubexpressionsOfCoxeterWordByEndpoint,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
function( W, x )
  local subs, endpoints, fibers, a;
  subs := SubexpressionsOfCoxeterWord( W, x );
  endpoints := Set( List( subs, a -> a[2] ) );
  fibers := List( endpoints, w -> [ ] );
  for a in subs do
    Add( fibers[ Position( endpoints, a[2] ) ], a[1] );
  od;
  return rec( endpoints := endpoints, fibers := fibers );
end );

##
# Only the groups of subexpressions of x and of y with the same
# endpoint w are compared, instead of all the pairs.
InstallMethod( DoubleLeavesIndicesOfHom,
  "for a Coxeter group and two words",
  [ IsCoxeterGroup, IsList, IsList ],
function( W, x, y )
  local gx, gy, res, j, p, w, e, f;
  gx := SubexpressionsOfCoxeterWordByEndpoint( W, x );
  gy := SubexpressionsOfCoxeterWordByEndpoint( W, y );
  res := [ ];
  for j in [ 1 .. Length( gx.endpoints ) ] do
    w := gx.endpoints[j];
    p := Position( gy.endpoints, w );
    if p <> fail then
      for e in gx.fibers[j] do
        for f in gy.fibers[p] do
          Add( res, [ e, f, w ] );
        od;
      od;
    fi;
  od;
  Sort( res );
  return res;
end );
