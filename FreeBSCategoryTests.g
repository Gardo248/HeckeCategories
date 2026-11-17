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
TnsM := TensorProductOnMorphisms;
IdM := IdentityMorphism;

W := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] ); # A2
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
ST := m -> [ BSWord( Source( m ) ), BSWord( Target( m ) ) ];
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
g := TnsM( IdM( Ob( [2,1] ) ), EndDot( D, 2 ) );    # [2,1,2] -> [2,1]
h := TnsM( IdM( Ob( [2] ) ), sp1 );                 # [2,1]   -> [2,1,1]
Check( "associativity of composition",
       EqM( PreCompose( PreCompose( f, g ), h ), PreCompose( f, PreCompose( g, h ) ) ) );
Check( "left identity",  EqM( PreCompose( IdM( Source( f ) ), f ), f ) );
Check( "right identity", EqM( PreCompose( f, IdM( Target( f ) ) ), f ) );
Check( "source/target of the composition",
       BSWord( Source( PreCompose( f, g ) ) ) = [1,2,1] and BSWord( Target( PreCompose( f, g ) ) ) = [2,1] );

# monoidal axioms
Check( "associativity of the tensor", EqM( TnsM( TnsM( f, g ), h ), TnsM( f, TnsM( g, h ) ) ) );
Check( "id_x (x) id_y = id_xy", EqM( TnsM( IdM( Ob( [1] ) ), IdM( Ob( [2,1] ) ) ), IdM( Ob( [1,2,1] ) ) ) );
Check( "id_unit (x) f = f", EqM( TnsM( IdM( TensorUnit( D ) ), f ), f ) );
Check( "f (x) id_unit = f", EqM( TnsM( f, IdM( TensorUnit( D ) ) ), f ) );
Check( "interchange law (1)",
       EqM( PreCompose( TnsM( f, IdM( Source( g ) ) ), TnsM( IdM( Target( f ) ), g ) ), TnsM( f, g ) ) );
Check( "interchange law (2)",
       EqM( PreCompose( TnsM( IdM( Source( f ) ), g ), TnsM( f, IdM( Target( g ) ) ) ), TnsM( f, g ) ) );
Check( "interchange law: (id_ss (x) merge) ; (merge (x) id_s) = merge (x) merge",
       EqM( PreCompose( TnsM( IdM( Ob( [1,1] ) ), mg1 ), TnsM( mg1, IdM( Ob( [1] ) ) ) ), TnsM( mg1, mg1 ) ) );
a1 := sp1;  b1 := mg1;  a2 := EndDot( D, 2 );  b2 := StartDot( D, 2 );
Check( "functoriality of the tensor",
       EqM( TnsM( PreCompose( a1, b1 ), PreCompose( a2, b2 ) ),
            PreCompose( TnsM( a1, a2 ), TnsM( b1, b2 ) ) ) );
Check( "the tensor is not commutative", BSCanonicalLayers( TnsM( f, h ) ) <> BSCanonicalLayers( TnsM( h, f ) ) );
Check( "zigzag (split (x) id) ; (id (x) merge) <> id_ss",
       not EqM( PreCompose( TnsM( sp1, IdM( Ob( [1] ) ) ), TnsM( IdM( Ob( [1] ) ), mg1 ) ), IdM( Ob( [1,1] ) ) ) );

# equality does not depend on the order of independent layers
Check( "MorphismConstructor: layers in another order give an equal morphism",
       EqM( MorphismConstructor( D, Ob( [1,1,1,1] ),
              [ [ 2, [1,1], [1], [ "TrivalentVertex", 1 ] ], [ 0, [1,1], [1], [ "TrivalentVertex", 1 ] ] ],
              Ob( [1,1] ) ),
            TnsM( mg1, mg1 ) ) );

# lazy normalization: BSLayers is stored as it comes, BSCanonicalLayers
# is computed only when needed
# (CAP caches the results of the operations: m0 must be a morphism never
#  built before, otherwise it could be an old object already normalized)
m0 := TnsM( SplitVertex( D, 2 ), MergeVertex( D, 2 ) );
Check( "lazy: the canonical form is not computed at construction", not HasBSCanonicalLayers( m0 ) );
m1 := PreCompose( TnsM( mg1, IdM( Ob( [1,1] ) ) ), TnsM( IdM( Ob( [1] ) ), mg1 ) );   # (f (x) id) ; (id (x) g)
m2 := PreCompose( TnsM( IdM( Ob( [1,1] ) ), mg1 ), TnsM( mg1, IdM( Ob( [1] ) ) ) );   # (id (x) g) ; (f (x) id)
Check( "(merge (x) id) ; (id (x) merge) = (id (x) merge) ; (merge (x) id)", EqM( m1, m2 ) );
Check( "... with different BSLayers", BSLayers( m1 ) <> BSLayers( m2 ) );
Check( "... and the same BSCanonicalLayers", BSCanonicalLayers( m1 ) = BSCanonicalLayers( m2 ) );
fs := sp12;  gs := EndDot( D, 2 );                  # [1,2,1] -> [2,1,2],  [2] -> []
n1 := PreCompose( TnsM( fs, IdM( Ob( [2] ) ) ), TnsM( IdM( Target( fs ) ), gs ) );
n2 := PreCompose( TnsM( IdM( Source( fs ) ), gs ), TnsM( fs, IdM( TensorUnit( D ) ) ) );
Check( "(Spider (x) id) ; (id (x) EndDot) = (id (x) EndDot) ; (Spider (x) id)", EqM( n1, n2 ) );
Check( "... with different BSLayers and the same BSCanonicalLayers",
       BSLayers( n1 ) <> BSLayers( n2 ) and BSCanonicalLayers( n1 ) = BSCanonicalLayers( n2 ) );
Check( "same generators in an order not allowed by the interchange law -> different",
       not EqM( PreCompose( TnsM( sp1, IdM( Ob( [1] ) ) ), TnsM( IdM( Ob( [1] ) ), mg1 ) ),
                PreCompose( TnsM( IdM( Ob( [1] ) ), sp1 ), TnsM( mg1, IdM( Ob( [1] ) ) ) ) ) );

# cases with empty parts (morphisms from/to the unit)
dot := ed1;  udot := sd1;
Check( "dot (x) udot = udot o dot", EqM( TnsM( dot, udot ), PreCompose( dot, udot ) ) );
Check( "udot (x) dot = udot o dot", EqM( TnsM( udot, dot ), PreCompose( dot, udot ) ) );
Check( "udot o dot <> id_s", not EqM( PreCompose( dot, udot ), IdM( Ob( [1] ) ) ) );
sc := PreCompose( udot, dot );                              # barbell: endomorphism of the unit
Check( "scalar <> id of the unit", not EqM( sc, IdM( TensorUnit( D ) ) ) );
Check( "scalar on the left <> on the right of a strand (no braiding)",
       not EqM( TnsM( sc, IdM( Ob( [1] ) ) ), TnsM( IdM( Ob( [1] ) ), sc ) ) );
Check( "scalars: sc (x) sc = sc o sc", EqM( TnsM( sc, sc ), PreCompose( sc, sc ) ) );

# in Syn (purely syntactic equality) composition is NOT
# associative: the two trees are different. This test documents the fact.
Syn := ModelingCategory( D );
mf := ModelingMorphism( D, f );  mg := ModelingMorphism( D, g );  mh := ModelingMorphism( D, h );
Check( "in Syn (f g) h and f (g h) are different terms",
       not IsEqualForMorphisms( Syn, PreCompose( Syn, PreCompose( Syn, mf, mg ), mh ),
                                     PreCompose( Syn, mf, PreCompose( Syn, mg, mh ) ) ) );

# canonical form directly
Check( "FreeBSCanonicalLayers idempotent",
       FreeBSCanonicalLayers( BSCanonicalLayers( TnsM( f, g ) ) ) = BSCanonicalLayers( TnsM( f, g ) ) );

# ---------- systematic check of the axioms of strict monoidal category ----------
# The axioms are guaranteed by the construction, but are checked here on a
# family of morphisms (all the generators, some identities, some composites)
# and on ALL the composable/tensorable tuples of it.
# Since the category is strict, associators and unitors are identities
# (CAP does not even provide them for D): pentagon and triangle are trivial.
# The essential point is that equality is NOT syntactic (interchange law),
# so we also check that it is an equivalence relation compatible with
# PreCompose and TensorProductOnMorphisms (congruence).
CheckAll := function( name, tuples, pred )
  local bad;
  bad := First( tuples, t -> not CallFuncList( pred, t ) );
  Check( Concatenation( name, " (", String( Length( tuples ) ), " cases)" ), bad = fail );
  if bad <> fail then Print( "   counterexample: ", List( bad, x -> [ ST( x ), BSLayers( x ) ] ), "\n" ); fi;
end;
EqO := IsEqualForObjects;
TnsO := TensorProductOnObjects;
I := TensorUnit( D );
objs := List( [ [], [1], [2], [1,2], [2,1,1] ], Ob );
sample := Concatenation( gens,
  List( objs{[ 1 .. 3 ]}, IdM ),
  [ sc, m1, n1, PreCompose( sp1, mg1 ), TnsM( ed1, sd1 ), TnsM( sp12, sp1 ) ] );
small := Concatenation( gens{[ 1 .. 4 ]}, [ sp12, sc, IdM( Ob( [2] ) ), IdM( I ) ] );
Composable := { a, b } -> EqO( Target( a ), Source( b ) );
pairs  := Cartesian( sample, sample );
cpairs := Filtered( pairs, p -> Composable( p[1], p[2] ) );
ctriples := Concatenation( List( cpairs, p -> List( Filtered( sample, c -> Composable( p[2], c ) ),
                                                     c -> [ p[1], p[2], c ] ) ) );
Check( "there are enough composable triples", Length( ctriples ) >= 20 );

# well-definedness: the layers fit the source and end in the target
WellDef := IsWellDefinedForMorphisms;
CheckAll( "well-defined objects", List( objs, o -> [ o ] ), IsWellDefinedForObjects );
CheckAll( "well-defined (sample)", List( sample, m -> [ m ] ), WellDef );
CheckAll( "well-defined (compositions)", cpairs, { a, b } -> WellDef( PreCompose( a, b ) ) );
CheckAll( "well-defined (tensor products)", Cartesian( small, small ), { a, b } -> WellDef( TnsM( a, b ) ) );
Check( "IsWellDefined (generic CAP dispatcher) on an object and a morphism",
       IsWellDefined( Ob( [1,2] ) ) and IsWellDefined( sp12 ) );
# ill-defined cells, built bypassing the constructors (which would raise an error)
BadO := w -> CreateCapCategoryObjectWithAttributes( D, BSWord, w );
BadM := { S, layers, T } -> CreateCapCategoryMorphismWithAttributes( D, S, T, BSLayers, layers );
Check( "ill-defined object: letter out of range", not IsWellDefinedForObjects( BadO( [ 3 ] ) ) );
Check( "ill-defined object: not a list of integers", not IsWellDefinedForObjects( BadO( [ "s" ] ) ) );
Check( "ill-defined morphism: layer that does not fit the source",
       not WellDef( BadM( Ob( [2] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: invalid generator",
       not WellDef( BadM( Ob( [1] ), [ [ 0, [1], [], [ "TrivalentVertex", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: unknown label",
       not WellDef( BadM( Ob( [1] ), [ [ 0, [1], [], [ "Foo", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: wrong target",
       not WellDef( BadM( Ob( [1] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], Ob( [1] ) ) ) );
Check( "ill-defined morphism: malformed layer", not WellDef( BadM( Ob( [1] ), [ [ 0, [1] ] ], I ) ) );
Check( "ill-defined morphism: ill-defined source",
       not WellDef( BadM( BadO( [ 3 ] ), [ ], BadO( [ 3 ] ) ) ) );

# category: source/target, identities, associativity
CheckAll( "source/target of the identity", List( objs, o -> [ o ] ),
          o -> EqO( Source( IdM( o ) ), o ) and EqO( Target( IdM( o ) ), o ) );
CheckAll( "source/target of the composition", cpairs,
          { a, b } -> EqO( Source( PreCompose( a, b ) ), Source( a ) ) and
                      EqO( Target( PreCompose( a, b ) ), Target( b ) ) );
CheckAll( "identity laws", List( sample, m -> [ m ] ),
          m -> EqM( PreCompose( IdM( Source( m ) ), m ), m ) and EqM( PreCompose( m, IdM( Target( m ) ) ), m ) );
CheckAll( "associativity of composition", ctriples,
          { a, b, c } -> EqM( PreCompose( PreCompose( a, b ), c ), PreCompose( a, PreCompose( b, c ) ) ) );

# tensor on objects: strict associativity and unit
CheckAll( "associativity of the tensor on objects", Cartesian( objs, objs, objs ),
          { a, b, c } -> EqO( TnsO( TnsO( a, b ), c ), TnsO( a, TnsO( b, c ) ) ) );
CheckAll( "unit on objects (left and right)", List( objs, o -> [ o ] ),
          o -> EqO( TnsO( I, o ), o ) and EqO( TnsO( o, I ), o ) );

# tensor on morphisms: source/target, strict associativity and unit
CheckAll( "source/target of the tensor", Cartesian( small, small ),
          { a, b } -> EqO( Source( TnsM( a, b ) ), TnsO( Source( a ), Source( b ) ) ) and
                      EqO( Target( TnsM( a, b ) ), TnsO( Target( a ), Target( b ) ) ) );
# (each operation goes through Syn and back: the triples are taken from a
#  smaller family to keep the running time reasonable)
small3 := [ sd1, mg1, sp12, sc, IdM( I ) ];
CheckAll( "associativity of the tensor on morphisms", Cartesian( small3, small3, small3 ),
          { a, b, c } -> EqM( TnsM( TnsM( a, b ), c ), TnsM( a, TnsM( b, c ) ) ) );
CheckAll( "unit on morphisms (left and right)", List( sample, m -> [ m ] ),
          m -> EqM( TnsM( IdM( I ), m ), m ) and EqM( TnsM( m, IdM( I ) ), m ) );

# tensor is a bifunctor
CheckAll( "id_a (x) id_b = id_(a (x) b)", Cartesian( objs, objs ),
          { a, b } -> EqM( TnsM( IdM( a ), IdM( b ) ), IdM( TnsO( a, b ) ) ) );
# composable pairs with at most 2 layers in all (the canonical form costs up
# to k! for k independent layers)
cpairs_small := [ [ sd1, ed1 ], [ ed1, sd1 ], [ sp1, mg1 ], [ mg1, sp1 ], [ sp12, sp21 ],
                  [ IdM( Ob( [2] ) ), EndDot( D, 2 ) ], [ sd1, sp1 ], [ IdM( I ), IdM( I ) ] ];
CheckAll( "functoriality: (a1 a2) (x) (b1 b2) = (a1 (x) b1)(a2 (x) b2)",
          List( Cartesian( cpairs_small, cpairs_small ), q -> Concatenation( q[1], q[2] ) ),
          { a1, a2, b1, b2 } -> EqM( TnsM( PreCompose( a1, a2 ), PreCompose( b1, b2 ) ),
                                     PreCompose( TnsM( a1, b1 ), TnsM( a2, b2 ) ) ) );
CheckAll( "interchange: (a (x) id)(id (x) b) = a (x) b = (id (x) b)(a (x) id)", Cartesian( small, small ),
          { a, b } -> EqM( PreCompose( TnsM( a, IdM( Source( b ) ) ), TnsM( IdM( Target( a ) ), b ) ), TnsM( a, b ) ) and
                      EqM( PreCompose( TnsM( IdM( Source( a ) ), b ), TnsM( a, IdM( Target( b ) ) ) ), TnsM( a, b ) ) );

# equality: equivalence relation and congruence
CheckAll( "equality is reflexive", List( sample, m -> [ m ] ), m -> EqM( m, m ) );
CheckAll( "equality is symmetric", Filtered( pairs, p -> EqO( Source( p[1] ), Source( p[2] ) ) and
                                                      EqO( Target( p[1] ), Target( p[2] ) ) ),
          { a, b } -> EqM( a, b ) = EqM( b, a ) );
# three different representatives of dot (x) dot (x) dot : [1,1,1] -> []
# (with 2 layers there are only 2 orders: 3 independent layers are needed)
dl := p -> [ p, [1], [], [ "Dot", 1 ] ];
r1 := TnsM( TnsM( ed1, ed1 ), ed1 );                                       # left, middle, right
r2 := MorphismConstructor( D, Ob( [1,1,1] ), [ dl( 2 ), dl( 1 ), dl( 0 ) ], I ); # right, middle, left
r3 := MorphismConstructor( D, Ob( [1,1,1] ), [ dl( 1 ), dl( 0 ), dl( 0 ) ], I ); # middle, left, right
Check( "three distinct representatives", Length( Set( [ BSLayers( r1 ), BSLayers( r2 ), BSLayers( r3 ) ] ) ) = 3 );
Check( "equality is transitive (r1 = r2, r2 = r3, r1 = r3)", EqM( r1, r2 ) and EqM( r2, r3 ) and EqM( r1, r3 ) );
# equal morphisms with different layers stay equal after o and (x)
q1 := TnsM( mg1, mg1 );
q2 := PreCompose( TnsM( IdM( Ob( [1,1] ) ), mg1 ), TnsM( mg1, IdM( Ob( [1] ) ) ) );
Check( "q1, q2 have different layers", BSLayers( q1 ) <> BSLayers( q2 ) );
reps := [ [ q1, q2 ], [ r1, r2 ], [ r2, r3 ], [ m1, m2 ], [ n1, n2 ] ];
# morphisms that end in the sources of the representatives
into := Concatenation( sample, [ TnsM( sp1, sp1 ),                        # [1,1] -> [1,1,1,1]
                                 TnsM( sp1, IdM( Ob( [1] ) ) ),           # [1,1] -> [1,1,1]
                                 TnsM( sp21, StartDot( D, 2 ) ) ] );     # [2,1,2] -> [1,2,1,2]
CheckAll( "congruence for PreCompose (on the right)",
          Concatenation( List( reps, p -> List( Filtered( sample, c -> Composable( p[1], c ) ), c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> EqM( PreCompose( a, c ), PreCompose( b, c ) ) );
CheckAll( "congruence for PreCompose (on the left)",
          Concatenation( List( reps, p -> List( Filtered( into, c -> Composable( c, p[1] ) ), c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> EqM( PreCompose( c, a ), PreCompose( c, b ) ) );
CheckAll( "congruence for the tensor (both sides)",
          Concatenation( List( reps, p -> List( small, c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> EqM( TnsM( a, c ), TnsM( b, c ) ) and EqM( TnsM( c, a ), TnsM( c, b ) ) );

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
