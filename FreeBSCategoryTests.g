#############################################################
# FreeBSCategoryTests.g -- tests of FreeBSCategory
#   section 0: no floating point in FreeBSCategory.*
#   section 1: the CAP category FreeBSCategory( W )
# (the tests of the combinatorics of words are in test.g)
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

# ---------- 0. no floating point in the source files ----------
for f in [ "FreeBSCategory.gd", "FreeBSCategory.gi" ] do
  txt := StringFile( f );
  Check( Concatenation( f, ": no Float" ),
         PositionSublist( txt, "Float" ) = fail and
         PositionSublist( txt, "FLOAT" ) = fail and
         PositionSublist( txt, "Cos(" ) = fail );
od;

# ---------- 1. the CAP category FreeBSCategory ----------
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
