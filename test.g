#############################################################
# test.g -- tests for coxeter.g
#
# Usage (from the directory of the files):   gap -q test.g
# or from GAP:                               Read("test.g");
#############################################################

Read("coxeter.g");

TEST_COUNT := 0;
TEST_FAILED := 0;

# Compares the obtained value with the expected one
CheckEqual := function(name, got, expected)
  TEST_COUNT := TEST_COUNT + 1;
  if got <> expected then
    TEST_FAILED := TEST_FAILED + 1;
    Print("FAIL: ", name, "\n   expected: ", expected, "\n   got: ", got, "\n");
  fi;
end;

# Checks that the call f(args) raises an error
CheckError := function(name, f, args)
  local res, old;
  TEST_COUNT := TEST_COUNT + 1;
  # without this, Error() enters the break loop instead of being caught
  old := BreakOnError;
  BreakOnError := false;
  res := CALL_WITH_CATCH(f, args);
  BreakOnError := old;
  if res[1] = true then
    TEST_FAILED := TEST_FAILED + 1;
    Print("FAIL: ", name, " (an error was expected)\n");
  fi;
end;

# ---- generators of Coxeter matrices -------------------------
# Chain diagram of length n, with labels `labels`
# (m_{i,i+1} = labels[i]); the other pairs have m = 2.
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

# Matrix from a list of edges [i,j,m]
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
# 1. Structure of the object
#############################################################
W := CoxeterGroupByMatrix([[1,3],[3,1]], ["s","t"]);
CheckEqual("IsCoxeterGroup", IsCoxeterGroup(W), true);
CheckEqual("IsGroup", IsGroup(W), true);
CheckEqual("CoxeterMatrix", CoxeterMatrix(W), [[1,3],[3,1]]);
CheckEqual("CoxeterGeneratorNames", CoxeterGeneratorNames(W), ["s","t"]);
CheckEqual("number of generators", Length(GeneratorsOfGroup(W)), 2);

W := CoxeterGroupByMatrix([[1,3,2],[3,1,3],[2,3,1]]);
CheckEqual("default names", CoxeterGeneratorNames(W), ["s1","s2","s3"]);

#############################################################
# 2. Relations
#############################################################
W := CoxeterGroupByMatrix(ChainMatrix(3, [3,4]));   # B3
CheckEqual("s^2 = e", ForAll(GeneratorsOfGroup(W), s -> s^2 = One(W)), true);
CheckEqual("(s1 s2)^3 = e",
  (GeneratorsOfGroup(W)[1]*GeneratorsOfGroup(W)[2])^3 = One(W), true);
CheckEqual("(s2 s3)^4 = e",
  (GeneratorsOfGroup(W)[2]*GeneratorsOfGroup(W)[3])^4 = One(W), true);
CheckEqual("(s1 s3)^2 = e",
  (GeneratorsOfGroup(W)[1]*GeneratorsOfGroup(W)[3])^2 = One(W), true);
CheckEqual("(s1 s2)^2 <> e",
  (GeneratorsOfGroup(W)[1]*GeneratorsOfGroup(W)[2])^2 = One(W), false);

#############################################################
# 3. Orders of known finite groups
#############################################################
CheckEqual("rank 0",   Size(CoxeterGroupByMatrix([])), 1);
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
# D4: node 2 in the centre, connected to 1, 3, 4
CheckEqual("D4",
  Size(CoxeterGroupByMatrix(GraphMatrix(4, [[1,2,3],[2,3,3],[2,4,3]]))), 192);
# E6, E7, E8 (Bourbaki numbering)
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
# 4. Infinite groups
#############################################################
D := CoxeterGroupByMatrix([[1,infinity],[infinity,1]]);
CheckEqual("D_inf Size",     Size(D), infinity);
CheckEqual("D_inf IsFinite", IsFinite(D), false);
CheckEqual("D_inf gens",     Length(GeneratorsOfGroup(D)), 2);

A2t := CoxeterGroupByMatrix(GraphMatrix(3, [[1,2,3],[2,3,3],[1,3,3]]));
CheckEqual("A2 affine Size", Size(A2t), infinity);
CheckEqual("B2 affine (4,4,2)",
  IsFinite(CoxeterGroupByMatrix(GraphMatrix(3,[[1,2,4],[2,3,4]]))), false);
CheckEqual("hyperbolic (3,3,7)",
  IsFinite(CoxeterGroupByMatrix(GraphMatrix(3,[[1,2,3],[2,3,3],[1,3,7]]))),
  false);
CheckEqual("D4 affine",
  IsFinite(CoxeterGroupByMatrix(
    GraphMatrix(5,[[1,3,3],[2,3,3],[3,4,3],[3,5,3]]))), false);

#############################################################
# 5. Tests on the matrix (without building the group)
#############################################################
CheckEqual("IsFiniteCoxeterMatrix A3",
  IsFiniteCoxeterMatrix(ChainMatrix(3,[3,3])), true);
CheckEqual("IsFiniteCoxeterMatrix affine",
  IsFiniteCoxeterMatrix(GraphMatrix(3,[[1,2,3],[2,3,3],[1,3,3]])), false);

#############################################################
# 5b. Bilinear form (attribute of the group)
#############################################################
CheckEqual("bilinear form A2",
  CoxeterBilinearForm(CoxeterGroupByMatrix(ChainMatrix(2,[3]))),
  [[1,-1/2],[-1/2,1]]);
CheckEqual("bilinear form with infinity",
  CoxeterBilinearForm(CoxeterGroupByMatrix([[1,infinity],[infinity,1]])),
  [[1,-1],[-1,1]]);
CheckEqual("bilinear form m=2 (orthogonal)",
  CoxeterBilinearForm(CoxeterGroupByMatrix([[1,2],[2,1]])), [[1,0],[0,1]]);

#############################################################
# 6. Reflection representation
#############################################################
W := CoxeterGroupByMatrix(ChainMatrix(3,[3,3]));
rho := CoxeterReflectionRepresentation(W);
CheckEqual("rho injective (A3)", IsInjective(rho), true);
CheckEqual("rho |Im| (A3)", Size(Image(rho)), 24);
mats := CoxeterReflectionMatrices(W);
CheckEqual("reflections: order 2", ForAll(mats, A -> Order(A) = 2), true);
CheckEqual("reflections: det -1", ForAll(mats, A -> DeterminantMat(A) = -1), true);
CheckEqual("order s1 s2", Order(mats[1]*mats[2]), 3);
CheckEqual("order s1 s3", Order(mats[1]*mats[3]), 2);

# H3 (uses sqrt(5)): orders of the products
mats := CoxeterReflectionMatrices(CoxeterGroupByMatrix(ChainMatrix(3,[5,3])));
CheckEqual("H3 order s1 s2", Order(mats[1]*mats[2]), 5);
CheckEqual("H3 order s2 s3", Order(mats[2]*mats[3]), 3);
CheckEqual("H3 order s1 s3", Order(mats[1]*mats[3]), 2);

# the representation is a homomorphism (check on the product)
W := CoxeterGroupByMatrix(ChainMatrix(3,[3,4]));
rho := CoxeterReflectionRepresentation(W);
g := GeneratorsOfGroup(W);
CheckEqual("rho is a homomorphism",
  (g[1]*g[2]*g[3])^rho, g[1]^rho * g[2]^rho * g[3]^rho);

# infinite groups: the generators have the expected representation
# (IsInjective is not computed: it would not terminate on an infinite fp group)
D := CoxeterGroupByMatrix([[1,infinity],[infinity,1]]);
rho := CoxeterReflectionRepresentation(D);
CheckEqual("rho D_inf: s1 -> reflection",
  GeneratorsOfGroup(D)[1]^rho, [[-1,0],[2,1]]);
CheckEqual("rho D_inf: s2 -> reflection",
  GeneratorsOfGroup(D)[2]^rho, [[1,2],[0,-1]]);

#############################################################
# 7. Permutation representation (finite groups only)
#############################################################
W := CoxeterGroupByMatrix(ChainMatrix(3,[3,3]));
pi := CoxeterPermutationRepresentation(W);
CheckEqual("pi injective (A3)", IsInjective(pi), true);
CheckEqual("pi |Im| (A3)", Size(Image(pi)), 24);
CheckEqual("A3: 12 roots", LargestMovedPoint(Image(pi)), 12);

W := CoxeterGroupByMatrix(ChainMatrix(3,[5,3]));
CheckEqual("H3 pi injective", IsInjective(CoxeterPermutationRepresentation(W)), true);
CheckEqual("H3: 30 roots",
  LargestMovedPoint(Image(CoxeterPermutationRepresentation(W))), 30);

Print("(the following 'Error, ...' lines are EXPECTED errors, caught by the tests)\n");
CheckError("pi on an infinite group",
  CoxeterPermutationRepresentation, [D]);

#############################################################
# 8. Input validation errors
#############################################################
CheckError("not symmetric",
  CoxeterGroupByMatrix, [[[1,3],[4,1]]]);
CheckError("diagonal <> 1",
  CoxeterGroupByMatrix, [[[2,3],[3,1]]]);
CheckError("off-diagonal entry = 1",
  CoxeterGroupByMatrix, [[[1,1],[1,1]]]);
CheckError("off-diagonal entry = 0",
  CoxeterGroupByMatrix, [[[1,0],[0,1]]]);
CheckError("negative entry",
  CoxeterGroupByMatrix, [[[1,-3],[-3,1]]]);
CheckError("non-integer entry",
  CoxeterGroupByMatrix, [[[1,5/2],[5/2,1]]]);
CheckError("non-square matrix",
  CoxeterGroupByMatrix, [[[1,3,2],[3,1,2]]]);
CheckError("names: wrong number",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], ["s"]]);
CheckError("names: duplicates",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], ["s","s"]]);
CheckError("names: not strings",
  CoxeterGroupByMatrix, [[[1,3],[3,1]], [1,2]]);

#############################################################
# Combinatorics of words (sections 9-13)
#############################################################

# Checks that the condition cond holds
Check := function(name, cond)
  TEST_COUNT := TEST_COUNT + 1;
  if not cond then
    TEST_FAILED := TEST_FAILED + 1;
    Print("FAIL: ", name, "\n");
  fi;
end;
Bits := function( s ) return List( [ 1 .. Length( s ) ], i -> Int( [ s[i] ] ) ); end;
T := function( e, f, w ) return [ Bits( e ), Bits( f ), w ]; end;

#############################################################
# 9. S_3
#############################################################
W := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] );
s := 1; t := 2;
Check( "NF ss = e", CoxeterNormalFormOfWord( W, [s,s] ) = [] );
Check( "NF sts = tst", CoxeterNormalFormOfWord( W, [s,t,s] ) = CoxeterNormalFormOfWord( W, [t,s,t] ) );
Check( "NF sts = [1,2,1]", CoxeterNormalFormOfWord( W, [t,s,t] ) = [1,2,1] );
Check( "|I(sts)| = 3", Length( InversionSetOfCoxeterWord( W, [s,t,s] ) ) = 3 );
Check( "Hom(e,e)", DoubleLeavesIndicesOfHom( W, [], [] ) = [ [ [], [], [] ] ] );
Check( "Hom(s,s)", Set( DoubleLeavesIndicesOfHom( W, [s], [s] ) ) = Set( [ T("0","0",[]), T("1","1",[1]) ] ) );
Check( "Hom(t,t)", Set( DoubleLeavesIndicesOfHom( W, [t], [t] ) ) = Set( [ T("0","0",[]), T("1","1",[2]) ] ) );
Check( "Hom(ss,s)", Set( DoubleLeavesIndicesOfHom( W, [s,s], [s] ) ) =
      Set( [ T("00","0",[]), T("11","0",[]), T("10","1",[1]), T("01","1",[1]) ] ) );
user := [ ["000","000",[]],["101","000",[]],["000","110",[]],["101","110",[]],
          ["000","101",[]],["101","101",[]],["000","011",[]],["101","011",[]],
          ["100","100",[1]],["100","010",[1]],["100","001",[1]],["100","111",[1]],
          ["001","100",[1]],["001","010",[1]],["001","001",[1]],["001","111",[1]] ];
user := List( user, a -> T( a[1], a[2], a[3] ) );
got := DoubleLeavesIndicesOfHom( W, [s,t,s], [s,s,s] );
Check( "Hom(sts,sss): 16 generators as in the list", Length( got ) = 16 and Set( got ) = Set( user ) );

#############################################################
# 10. Comparison with the EXACT oracle of the fp group (finite groups)
#############################################################
# (equality in a finite fp group = coset enumeration, exact arithmetic)
CheckAgainstFp := function( M, name, N, L )
  local W, gens, n, k, w1, w2, nf1, same, el;
  W := CoxeterGroupByMatrix( M );  gens := GeneratorsOfGroup( W );  n := Length( M );
  el := w -> Product( gens{ w }, One( W ) );
  for k in [ 1 .. N ] do
    w1 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    w2 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    same := ( el( w1 ) = el( w2 ) );
    Check( Concatenation( name, ": equal NF <=> equal elements" ),
           same = ( CoxeterNormalFormOfWord( W, w1 ) = CoxeterNormalFormOfWord( W, w2 ) ) );
    nf1 := CoxeterNormalFormOfWord( W, w1 );
    Check( Concatenation( name, ": NF is a word for the same element" ), el( nf1 ) = el( w1 ) );
    Check( Concatenation( name, ": NF not longer, same parity" ),
           Length( nf1 ) <= Length( w1 ) and ( Length( w1 ) - Length( nf1 ) ) mod 2 = 0 );
    Check( Concatenation( name, ": |I(w)| = length of NF" ),
           Length( InversionSetOfCoxeterWord( W, w1 ) ) = Length( nf1 ) );
    Check( Concatenation( name, ": NF idempotent" ), CoxeterNormalFormOfWord( W, nf1 ) = nf1 );
    Check( Concatenation( name, ": w * w^-1 = e" ),
           CoxeterNormalFormOfWord( W, Concatenation( w1, Reversed( w1 ) ) ) = [] );
  od;
end;
CheckAgainstFp( [[1,3,2],[3,1,3],[2,3,1]], "A3", 150, 9 );
CheckAgainstFp( [[1,3,2],[3,1,4],[2,4,1]], "B3", 150, 9 );
CheckAgainstFp( [[1,3,2],[3,1,5],[2,5,1]], "H3", 80, 9 );   # uses sqrt(5)
CheckAgainstFp( [[1,5],[5,1]], "I2(5)", 60, 10 );
CheckAgainstFp( [[1,7],[7,1]], "I2(7)", 60, 12 );           # uses cos(pi/7)

#############################################################
# 11. Infinite groups: comparison with the EXACT equality of the Tits matrices
#############################################################
CheckAgainstTits := function( M, name, N, L, infinite_irreducible )
  local mats, n, k, w1, w2, W, mat, same;
  W := CoxeterGroupByMatrix( M );  mats := CoxeterReflectionMatrices( W );  n := Length( M );
  mat := w -> Product( mats{ w }, IdentityMat( n ) );
  for k in [ 1 .. N ] do
    w1 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    w2 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    same := ( mat( w1 ) = mat( w2 ) );
    Check( Concatenation( name, ": equal NF <=> equal Tits matrices" ),
           same = ( CoxeterNormalFormOfWord( W, w1 ) = CoxeterNormalFormOfWord( W, w2 ) ) );
    Check( Concatenation( name, ": NF = same matrix" ),
           mat( CoxeterNormalFormOfWord( W, w1 ) ) = mat( w1 ) );
    Check( Concatenation( name, ": w * w^-1 = e" ),
           CoxeterNormalFormOfWord( W, Concatenation( w1, Reversed( w1 ) ) ) = [] );
  od;
  # in an infinite irreducible Coxeter group the powers of a Coxeter
  # element are reduced (Speyer)
  if infinite_irreducible then
    w1 := Concatenation( List( [ 1 .. 6 ], i -> [ 1 .. n ] ) );
    Check( Concatenation( name, ": (s1...sn)^6 is reduced" ),
           Length( CoxeterNormalFormOfWord( W, w1 ) ) = 6 * n );
  fi;
end;
CheckAgainstTits( [[1,3,3],[3,1,3],[3,3,1]], "affine A2~", 150, 14, true );
CheckAgainstTits( [[1,4,2],[4,1,4],[2,4,1]], "affine B2~", 150, 14, true );
CheckAgainstTits( [[1,3,7],[3,1,3],[7,3,1]], "hyperbolic (7,3,3)", 100, 14, true );
CheckAgainstTits( [[1,3,2,2],[3,1,3,3],[2,3,1,2],[2,3,2,1]], "D4 (finite, via Tits)", 100, 12, false );

#############################################################
# 12. Infinite group: hand count
#############################################################
W := CoxeterGroupByMatrix( [[1,4,2],[4,1,4],[2,4,1]] );
Check( "affine B2~, Hom(121,121) has 12 generators", Length( DoubleLeavesIndicesOfHom( W, [1,2,1], [1,2,1] ) ) = 12 );
Check( "affine B2~, braid m=4", CoxeterNormalFormOfWord( W, [1,2,1,2] ) = CoxeterNormalFormOfWord( W, [2,1,2,1] ) );
Check( "affine B2~, commutation", CoxeterNormalFormOfWord( W, [1,3] ) = CoxeterNormalFormOfWord( W, [3,1] ) );
Check( "affine B2~, 121 <> 212", CoxeterNormalFormOfWord( W, [1,2,1] ) <> CoxeterNormalFormOfWord( W, [2,1,2] ) );

#############################################################
# 13. Errors in the combinatorics
#############################################################
CheckError("letter out of range -> error",
  CoxeterNormalFormOfWord, [CoxeterGroupByMatrix([[1,3],[3,1]]), [3]]);

#############################################################
# Summary
#############################################################
Print("\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " tests passed");
if TEST_FAILED = 0 then
  Print(" -- ALL OK\n");
else
  Print(" -- ", TEST_FAILED, " FAILED\n");
fi;
