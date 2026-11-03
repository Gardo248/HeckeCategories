#############################################################
# FreeBSCategoryTests.g -- tests of FreeBSCategory
#   sections 0-5: combinatorial level
#   section 6:    the CAP category FreeBSCategory( W )
# Usage (WSL terminal, from the directory of the files):
#   gap -q FreeBSCategoryTests.g < /dev/null > tests_output.txt
#############################################################
Read( "FreeBSCategory.g" );
Print( "(the \"Error, ...\" lines printed below are EXPECTED errors, caught by the tests)\n" );

TEST_COUNT := 0;  TEST_FAILED := 0;
Check := function( name, cond )
  TEST_COUNT := TEST_COUNT + 1;
  if not cond then TEST_FAILED := TEST_FAILED + 1; Print( "FAIL: ", name, "\n" ); fi;
end;
Bits := function( s ) return List( [ 1 .. Length( s ) ], i -> Int( [ s[i] ] ) ); end;
T := function( e, f, w ) return [ Bits( e ), Bits( f ), w ]; end;

# ---------- 0. no floating point in the source files ----------
for f in [ "FreeBSCategory.gd", "FreeBSCategory.gi" ] do
  txt := StringFile( f );
  Check( Concatenation( f, ": no Float" ),
         PositionSublist( txt, "Float" ) = fail and
         PositionSublist( txt, "FLOAT" ) = fail and
         PositionSublist( txt, "Cos(" ) = fail );
od;

# ---------- 1. S_3 ----------
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

# ---------- 2. comparison with the EXACT oracle of the fp group (finite groups) ----------
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

# ---------- 3. infinite groups: comparison with the EXACT equality of the Tits matrices ----------
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

# ---------- 4. infinite group: hand count ----------
W := CoxeterGroupByMatrix( [[1,4,2],[4,1,4],[2,4,1]] );
Check( "affine B2~, Hom(121,121) has 12 generators", Length( DoubleLeavesIndicesOfHom( W, [1,2,1], [1,2,1] ) ) = 12 );
Check( "affine B2~, braid m=4", CoxeterNormalFormOfWord( W, [1,2,1,2] ) = CoxeterNormalFormOfWord( W, [2,1,2,1] ) );
Check( "affine B2~, commutation", CoxeterNormalFormOfWord( W, [1,3] ) = CoxeterNormalFormOfWord( W, [3,1] ) );
Check( "affine B2~, 121 <> 212", CoxeterNormalFormOfWord( W, [1,2,1] ) <> CoxeterNormalFormOfWord( W, [2,1,2] ) );

# ---------- 5. errors ----------
W := CoxeterGroupByMatrix( [[1,3],[3,1]] );
old := BreakOnError;  BreakOnError := false;
res := CALL_WITH_CATCH( CoxeterNormalFormOfWord, [ W, [3] ] );
BreakOnError := old;
Check( "letter out of range -> error", res[1] = false );


# ---------- 6. the CAP category FreeBSCategory ----------
CheckErr := function( name, f )
  local old, res;
  old := BreakOnError;  BreakOnError := false;
  res := CALL_WITH_CATCH( f, [ ] );
  BreakOnError := old;
  Check( name, res[1] = false );
end;
EqM := IsEqualForMorphisms;
Tns := TensorProductOnMorphisms;
IdM := IdentityMorphism;

W := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] );
D := FreeBSCategory( W );
Ob := w -> BSObject( D, w );
Check( "IsFreeBSCategory", IsFreeBSCategory( D ) );
Check( "IsStrictMonoidalCategory", IsStrictMonoidalCategory( D ) );

# objects
Check( "tensor of objects", BSWord( TensorProductOnObjects( Ob( [1] ), Ob( [2,1] ) ) ) = [ 1, 2, 1 ] );
Check( "unit = empty word", BSWord( TensorUnit( D ) ) = [ ] );
Check( "unit is neutral", IsEqualForObjects( TensorProductOnObjects( TensorUnit( D ), Ob( [1,2] ) ), Ob( [1,2] ) ) );

# generators of Hom
hom := LightLeafMorphisms( D, [1,2,1], [1,1,1] );
Check( "Hom(sts,sss): 16 generators", Length( hom ) = 16 );
Check( "distinct generators",
       ForAll( Combinations( [ 1 .. 16 ], 2 ), p -> not EqM( hom[p[1]], hom[p[2]] ) ) );
Check( "source and target of the generators",
       ForAll( hom, h -> BSWord( Source( h ) ) = [1,2,1] and BSWord( Range( h ) ) = [1,1,1] ) );
Check( "number of generators = DoubleLeavesIndicesOfHom",
       ForAll( [ [ [], [] ], [ [1], [1] ], [ [1,1], [1] ], [ [1,2,1], [2,1,2] ] ],
               p -> Length( LightLeafMorphisms( D, p[1], p[2] ) ) =
                    Length( DoubleLeavesIndicesOfHom( W, p[1], p[2] ) ) ) );

dot  := LightLeafMorphism( D, [1], [], [ [0], [], [] ] );   # s -> empty
udot := LightLeafMorphism( D, [], [1], [ [], [0], [] ] );   # empty -> s
Check( "datum of a generator", BSLayers( dot ) = [ [ 0, [1], [], [0], [], [] ] ] );
Check( "LL(s,s,1,1,s) = id_s", EqM( LightLeafMorphism( D, [1], [1], [ [1], [1], [1] ] ), IdM( Ob( [1] ) ) ) );
Check( "LL(e,e,-,-,e) = id of the unit",
       EqM( LightLeafMorphism( D, [], [], [ [], [], [] ] ), IdM( TensorUnit( D ) ) ) );
Check( "LL(ss,ss,11,11,e) = id_ss (non-reduced word)",
       EqM( LightLeafMorphism( D, [1,1], [1,1], [ [1,1], [1,1], [] ] ), IdM( Ob( [1,1] ) ) ) );
Check( "LL(sts,sts,111,111,sts) = id_sts",
       EqM( LightLeafMorphism( D, [1,2,1], [1,2,1], [ [1,1,1], [1,1,1], [1,2,1] ] ), IdM( Ob( [1,2,1] ) ) ) );
Check( "Hom(sts,sts): exactly one generator is the identity",
       Number( LightLeafMorphisms( D, [1,2,1], [1,2,1] ), m -> EqM( m, IdM( Ob( [1,2,1] ) ) ) ) = 1 );
Check( "LL(s,s,0,0,e) is not the identity",
       not EqM( LightLeafMorphism( D, [1], [1], [ [0], [0], [] ] ), IdM( Ob( [1] ) ) ) );

# category axioms
f := LightLeafMorphisms( D, [1,2], [2,1] )[2];
g := LightLeafMorphisms( D, [2,1], [1] )[1];
h := LightLeafMorphisms( D, [1], [1,1] )[1];
Check( "associativity of composition",
       EqM( PreCompose( PreCompose( f, g ), h ), PreCompose( f, PreCompose( g, h ) ) ) );
Check( "left identity",  EqM( PreCompose( IdM( Source( f ) ), f ), f ) );
Check( "right identity", EqM( PreCompose( f, IdM( Range( f ) ) ), f ) );
Check( "source/target of the composition",
       BSWord( Source( PreCompose( f, g ) ) ) = [1,2] and BSWord( Range( PreCompose( f, g ) ) ) = [1] );

# monoidal axioms
Check( "associativity of the tensor", EqM( Tns( Tns( f, g ), h ), Tns( f, Tns( g, h ) ) ) );
Check( "id_x (x) id_y = id_xy", EqM( Tns( IdM( Ob( [1] ) ), IdM( Ob( [2,1] ) ) ), IdM( Ob( [1,2,1] ) ) ) );
Check( "id_unit (x) f = f", EqM( Tns( IdM( TensorUnit( D ) ), f ), f ) );
Check( "f (x) id_unit = f", EqM( Tns( f, IdM( TensorUnit( D ) ) ), f ) );
Check( "interchange law (1)",
       EqM( PreCompose( Tns( f, IdM( Source( g ) ) ), Tns( IdM( Range( f ) ), g ) ), Tns( f, g ) ) );
Check( "interchange law (2)",
       EqM( PreCompose( Tns( IdM( Source( f ) ), g ), Tns( f, IdM( Range( g ) ) ) ), Tns( f, g ) ) );
a1 := LightLeafMorphisms( D, [1], [1,1] )[2];  b1 := LightLeafMorphisms( D, [1,1], [] )[1];
a2 := LightLeafMorphisms( D, [2], [] )[1];     b2 := LightLeafMorphisms( D, [], [2,2] )[1];
Check( "functoriality of the tensor",
       EqM( Tns( PreCompose( a1, b1 ), PreCompose( a2, b2 ) ),
            PreCompose( Tns( a1, a2 ), Tns( b1, b2 ) ) ) );
Check( "the tensor is not commutative", BSLayers( Tns( f, h ) ) <> BSLayers( Tns( h, f ) ) );

# cases with empty parts (morphisms from/to the unit)
Check( "dot (x) udot = udot o dot", EqM( Tns( dot, udot ), PreCompose( dot, udot ) ) );
Check( "udot (x) dot = udot o dot", EqM( Tns( udot, dot ), PreCompose( dot, udot ) ) );
Check( "udot o dot <> id_s", not EqM( PreCompose( dot, udot ), IdM( Ob( [1] ) ) ) );
sc := PreCompose( udot, dot );                              # endomorphism of the unit
Check( "scalar <> id of the unit", not EqM( sc, IdM( TensorUnit( D ) ) ) );
Check( "scalar on the left <> on the right of a strand (no braiding)",
       not EqM( Tns( sc, IdM( Ob( [1] ) ) ), Tns( IdM( Ob( [1] ) ), sc ) ) );
Check( "scalars: sc (x) sc = sc o sc", EqM( Tns( sc, sc ), PreCompose( sc, sc ) ) );

# in Syn (purely syntactic equality) composition is NOT
# associative: the two trees are different. This test documents the fact.
Syn := ModelingCategory( D );
mf := ModelingMorphism( D, f );  mg := ModelingMorphism( D, g );  mh := ModelingMorphism( D, h );
Check( "in Syn (f g) h and f (g h) are different terms",
       not IsEqualForMorphisms( Syn, PreCompose( Syn, PreCompose( Syn, mf, mg ), mh ),
                                     PreCompose( Syn, mf, PreCompose( Syn, mg, mh ) ) ) );

# canonical form directly
Check( "FreeBSCanonicalLayers idempotent",
       FreeBSCanonicalLayers( BSLayers( Tns( f, g ) ) ) = BSLayers( Tns( f, g ) ) );

# an infinite group
W3 := CoxeterGroupByMatrix( [[1,3,3],[3,1,3],[3,3,1]] );
D3 := FreeBSCategory( W3 );
Check( "affine A2~: Hom(123,123)",
       Length( LightLeafMorphisms( D3, [1,2,3], [1,2,3] ) ) =
       Length( DoubleLeavesIndicesOfHom( W3, [1,2,3], [1,2,3] ) ) );

# errors
CheckErr( "invalid triple -> error", { } -> LightLeafMorphism( D, [1], [1], [ [1], [0], [1] ] ) );
CheckErr( "letter out of range -> error", { } -> BSObject( D, [ 3 ] ) );
CheckErr( "m = infinity -> error",
          { } -> FreeBSCategory( CoxeterGroupByMatrix( [[1,infinity],[infinity,1]] ) ) );

Print( "\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " tests passed" );
if TEST_FAILED = 0 then Print( " -- ALL OK\n" ); else Print( " -- ", TEST_FAILED, " FAILED\n" ); fi;
QUIT;
