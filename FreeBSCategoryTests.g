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

# generating morphisms
sd1  := StartDot( D, 1 );          # [] -> [1]
ed1  := EndDot( D, 1 );            # [1] -> []
sp1  := SplitVertex( D, 1 );       # [1] -> [1,1]
mg1  := MergeVertex( D, 1 );       # [1,1] -> [1]
sp12 := SpiderMorphism( D, 1, 2 ); # [1,2,1] -> [2,1,2]
sp21 := SpiderMorphism( D, 2, 1 ); # [2,1,2] -> [1,2,1]
ST := m -> [ BSWord( Source( m ) ), BSWord( Range( m ) ) ];
Check( "StartDot: [] -> [1]", ST( sd1 ) = [ [], [1] ] );
Check( "EndDot: [1] -> []", ST( ed1 ) = [ [1], [] ] );
Check( "SplitVertex: [1] -> [1,1]", ST( sp1 ) = [ [1], [1,1] ] );
Check( "MergeVertex: [1,1] -> [1]", ST( mg1 ) = [ [1,1], [1] ] );
Check( "Spider(1,2): [1,2,1] -> [2,1,2]", ST( sp12 ) = [ [1,2,1], [2,1,2] ] );
Check( "Spider(2,1): [2,1,2] -> [1,2,1]", ST( sp21 ) = [ [2,1,2], [1,2,1] ] );
Check( "datum of a generator", BSLayers( ed1 ) = [ [ 0, [1], [], [ "Dot", 1 ] ] ] );
Check( "BSGeneratingMorphism = EndDot",
       EqM( BSGeneratingMorphism( D, [1], [ "Dot", 1 ], [] ), ed1 ) );
gens := BSGeneratingMorphisms( D );
Check( "A2: 4*2 + 2 = 10 generators", Length( gens ) = 10 );
# (IsEqualForMorphisms needs equal sources and targets: compare the data)
Check( "distinct generators", IsDuplicateFreeList( List( gens, m -> [ ST( m ), BSLayers( m ) ] ) ) );
Check( "the generators are not identities", ForAll( gens, m -> Length( BSLayers( m ) ) = 1 ) );
W2 := CoxeterGroupByMatrix( [[1,2],[2,1]] );  D2 := FreeBSCategory( W2 );
Check( "A1xA1: Spider(1,2): [1,2] -> [2,1]", ST( SpiderMorphism( D2, 1, 2 ) ) = [ [1,2], [2,1] ] );

# freeness: no Soergel relation holds
Check( "split ; merge <> id_s", not EqM( PreCompose( sp1, mg1 ), IdM( Ob( [1] ) ) ) );
Check( "Spider(1,2) ; Spider(2,1) <> id_sts", not EqM( PreCompose( sp12, sp21 ), IdM( Ob( [1,2,1] ) ) ) );
Check( "merge ; split <> id_ss", not EqM( PreCompose( mg1, sp1 ), IdM( Ob( [1,1] ) ) ) );

# category axioms
f := sp12;                                         # [1,2,1] -> [2,1,2]
g := Tns( IdM( Ob( [2,1] ) ), EndDot( D, 2 ) );    # [2,1,2] -> [2,1]
h := Tns( IdM( Ob( [2] ) ), sp1 );                 # [2,1]   -> [2,1,1]
Check( "associativity of composition",
       EqM( PreCompose( PreCompose( f, g ), h ), PreCompose( f, PreCompose( g, h ) ) ) );
Check( "left identity",  EqM( PreCompose( IdM( Source( f ) ), f ), f ) );
Check( "right identity", EqM( PreCompose( f, IdM( Range( f ) ) ), f ) );
Check( "source/target of the composition",
       BSWord( Source( PreCompose( f, g ) ) ) = [1,2,1] and BSWord( Range( PreCompose( f, g ) ) ) = [2,1] );

# monoidal axioms
Check( "associativity of the tensor", EqM( Tns( Tns( f, g ), h ), Tns( f, Tns( g, h ) ) ) );
Check( "id_x (x) id_y = id_xy", EqM( Tns( IdM( Ob( [1] ) ), IdM( Ob( [2,1] ) ) ), IdM( Ob( [1,2,1] ) ) ) );
Check( "id_unit (x) f = f", EqM( Tns( IdM( TensorUnit( D ) ), f ), f ) );
Check( "f (x) id_unit = f", EqM( Tns( f, IdM( TensorUnit( D ) ) ), f ) );
Check( "interchange law (1)",
       EqM( PreCompose( Tns( f, IdM( Source( g ) ) ), Tns( IdM( Range( f ) ), g ) ), Tns( f, g ) ) );
Check( "interchange law (2)",
       EqM( PreCompose( Tns( IdM( Source( f ) ), g ), Tns( f, IdM( Range( g ) ) ) ), Tns( f, g ) ) );
Check( "interchange law: (id_ss (x) merge) ; (merge (x) id_s) = merge (x) merge",
       EqM( PreCompose( Tns( IdM( Ob( [1,1] ) ), mg1 ), Tns( mg1, IdM( Ob( [1] ) ) ) ), Tns( mg1, mg1 ) ) );
a1 := sp1;  b1 := mg1;  a2 := EndDot( D, 2 );  b2 := StartDot( D, 2 );
Check( "functoriality of the tensor",
       EqM( Tns( PreCompose( a1, b1 ), PreCompose( a2, b2 ) ),
            PreCompose( Tns( a1, a2 ), Tns( b1, b2 ) ) ) );
Check( "the tensor is not commutative", BSLayers( Tns( f, h ) ) <> BSLayers( Tns( h, f ) ) );
Check( "zigzag (split (x) id) ; (id (x) merge) <> id_ss",
       not EqM( PreCompose( Tns( sp1, IdM( Ob( [1] ) ) ), Tns( IdM( Ob( [1] ) ), mg1 ) ), IdM( Ob( [1,1] ) ) ) );

# the datum does not depend on the order of independent layers
Check( "MorphismConstructor canonicalises the layers",
       EqM( MorphismConstructor( D, Ob( [1,1,1,1] ),
              [ [ 2, [1,1], [1], [ "TrivalentVertex", 1 ] ], [ 0, [1,1], [1], [ "TrivalentVertex", 1 ] ] ],
              Ob( [1,1] ) ),
            Tns( mg1, mg1 ) ) );

# cases with empty parts (morphisms from/to the unit)
dot := ed1;  udot := sd1;
Check( "dot (x) udot = udot o dot", EqM( Tns( dot, udot ), PreCompose( dot, udot ) ) );
Check( "udot (x) dot = udot o dot", EqM( Tns( udot, dot ), PreCompose( dot, udot ) ) );
Check( "udot o dot <> id_s", not EqM( PreCompose( dot, udot ), IdM( Ob( [1] ) ) ) );
sc := PreCompose( udot, dot );                              # barbell: endomorphism of the unit
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

# infinite groups
W3 := CoxeterGroupByMatrix( [[1,3,3],[3,1,3],[3,3,1]] );
D3 := FreeBSCategory( W3 );
Check( "affine A2~: 4*3 + 6 = 18 generators", Length( BSGeneratingMorphisms( D3 ) ) = 18 );
Winf := CoxeterGroupByMatrix( [[1,infinity],[infinity,1]] );
Dinf := FreeBSCategory( Winf );
Check( "m = infinity: the category exists, 8 generators (no Spider)",
       Length( BSGeneratingMorphisms( Dinf ) ) = 8 );

# errors
CheckErr( "Spider with s = t -> error", { } -> SpiderMorphism( D, 1, 1 ) );
CheckErr( "Spider with m = infinity -> error", { } -> SpiderMorphism( Dinf, 1, 2 ) );
CheckErr( "unknown label -> error", { } -> BSGeneratingMorphism( D, [1], [ "Foo", 1 ], [] ) );
CheckErr( "Dot with wrong source/target -> error", { } -> BSGeneratingMorphism( D, [1], [ "Dot", 1 ], [1] ) );
CheckErr( "Spider in the wrong direction -> error",
          { } -> BSGeneratingMorphism( D, [1,2,1], [ "Spider", 2, 1 ], [2,1,2] ) );
CheckErr( "letter out of range -> error", { } -> BSObject( D, [ 3 ] ) );
CheckErr( "MorphismConstructor with an invalid layer -> error",
          { } -> MorphismConstructor( D, Ob( [1] ), [ [ 0, [1], [], [ "TrivalentVertex", 1 ] ] ], Ob( [] ) ) );
CheckErr( "MorphismConstructor with a wrong target -> error",
          { } -> MorphismConstructor( D, Ob( [1] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], Ob( [1] ) ) );

Print( "\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " tests passed" );
if TEST_FAILED = 0 then Print( " -- ALL OK\n" ); else Print( " -- ", TEST_FAILED, " FAILED\n" ); fi;
QUIT;
