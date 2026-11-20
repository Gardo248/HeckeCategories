#############################################################
# FreeBSCategoryTests.g -- tests of FreeBSCategory
#   section 0: no floating point in FreeBSCategory.*
#   section 1: the CAP category FreeBSCategory( W )
# (the tests of the combinatorics of words are in test.g)
# Usage (WSL terminal, from the directory of the files):
#   gap -q FreeBSCategoryTests.g < /dev/null > tests_output.txt 2>&1
#############################################################
Read( "FreeBSCategory.g" );

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
# CheckErr( name, f, expected ): passes iff f() raises an error whose message
# contains the substring expected.
# CALL_WITH_CATCH returns only [ false, 0 ] on error (no message): the message
# is captured by redirecting ERROR_OUTPUT to a string stream (this also keeps
# it out of the test output).
CheckErr := function( name, f, expected )
  local old_break, old_out, was_ro, msg, stream, res, ok;
  msg := "";
  stream := OutputTextString( msg, true );
  old_break := BreakOnError;  BreakOnError := false;
  old_out := ERROR_OUTPUT;
  was_ro := IsReadOnlyGlobal( "ERROR_OUTPUT" );
  if was_ro then MakeReadWriteGlobal( "ERROR_OUTPUT" ); fi;
  ERROR_OUTPUT := stream;
  res := CALL_WITH_CATCH( f, [ ] );
  ERROR_OUTPUT := old_out;
  if was_ro then MakeReadOnlyGlobal( "ERROR_OUTPUT" ); fi;
  BreakOnError := old_break;
  CloseStream( stream );
  ok := res[1] = false and PositionSublist( msg, expected ) <> fail;
  Check( name, ok );
  if not ok then
    if res[1] = false then
      Print( "   expected: \"", expected, "\"  got: ", Chomp( msg ), "\n" );
    else
      Print( "   expected: \"", expected, "\"  got: no error\n" );
    fi;
  fi;
end;

W := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] ); # A2
D := FreeBSCategory( W );
Ob := w -> BSObject( D, w );
Check( "IsFreeBSCategory", IsFreeBSCategory( D ) );
Check( "IsStrictMonoidalCategory", IsStrictMonoidalCategory( D ) );

# objects
Check( "tensor of objects", BSUnderlyingWord( TensorProductOnObjects( Ob( [1] ), Ob( [2,1] ) ) ) = [ 1, 2, 1 ] );
Check( "unit = empty word", BSUnderlyingWord( TensorUnit( D ) ) = [ ] );
Check( "unit is neutral", IsEqualForObjects( TensorProductOnObjects( TensorUnit( D ), Ob( [1,2] ) ), Ob( [1,2] ) ) );

# generating morphisms
upperdot := UpperDot( D, 1 );          # [] -> [1]
lowerdot := LowerDot( D, 1 );          # [1] -> []
split1   := SplitVertex( D, 1 );       # [1] -> [1,1]
merge1   := MergeVertex( D, 1 );       # [1,1] -> [1]
spider12 := SpiderMorphism( D, 1, 2 ); # [1,2,1] -> [2,1,2]
spider21 := SpiderMorphism( D, 2, 1 ); # [2,1,2] -> [1,2,1]
SourceTargetWords := m -> [ BSUnderlyingWord( Source( m ) ), BSUnderlyingWord( Target( m ) ) ];
Check( "UpperDot: [] -> [1]", SourceTargetWords( upperdot ) = [ [], [1] ] );
Check( "LowerDot: [1] -> []", SourceTargetWords( lowerdot ) = [ [1], [] ] );
Check( "SplitVertex: [1] -> [1,1]", SourceTargetWords( split1 ) = [ [1], [1,1] ] );
Check( "MergeVertex: [1,1] -> [1]", SourceTargetWords( merge1 ) = [ [1,1], [1] ] );
Check( "Spider(1,2): [1,2,1] -> [2,1,2]", SourceTargetWords( spider12 ) = [ [1,2,1], [2,1,2] ] );
Check( "Spider(2,1): [2,1,2] -> [1,2,1]", SourceTargetWords( spider21 ) = [ [2,1,2], [1,2,1] ] );
Check( "datum of a generator", BSLayers( lowerdot ) = [ [ 0, [1], [], [ "Dot", 1 ] ] ] );
Check( "BSGeneratingMorphism = LowerDot",
       IsEqualForMorphisms( BSGeneratingMorphism( D, [1], [ "Dot", 1 ], [] ), lowerdot ) );
gens := BSGeneratingMorphisms( D );
Check( "A2: 4*2 + 2 = 10 generators", Length( gens ) = 10 );
# (IsEqualForMorphisms needs equal sources and targets: compare the data)
Check( "distinct generators", IsDuplicateFreeList( List( gens, m -> [ SourceTargetWords( m ), BSLayers( m ) ] ) ) );
Check( "the generators are not identities", ForAll( gens, m -> Length( BSLayers( m ) ) = 1 ) );
W2 := CoxeterGroupByMatrix( [[1,2],[2,1]] );  D2 := FreeBSCategory( W2 );
Check( "A1xA1: Spider(1,2): [1,2] -> [2,1]", SourceTargetWords( SpiderMorphism( D2, 1, 2 ) ) = [ [1,2], [2,1] ] );

# category axioms
f := spider12;                                         # [1,2,1] -> [2,1,2]
g := TensorProductOnMorphisms( IdentityMorphism( Ob( [2,1] ) ), LowerDot( D, 2 ) );    # [2,1,2] -> [2,1]
h := TensorProductOnMorphisms( IdentityMorphism( Ob( [2] ) ), split1 );                 # [2,1]   -> [2,1,1]
Check( "associativity of composition",
       IsEqualForMorphisms( PreCompose( PreCompose( f, g ), h ), PreCompose( f, PreCompose( g, h ) ) ) );
Check( "source/target of the composition",
       BSUnderlyingWord( Source( PreCompose( f, g ) ) ) = [1,2,1] and BSUnderlyingWord( Target( PreCompose( f, g ) ) ) = [2,1] );

# monoidal axioms
# (identity laws, associativity and unit of the tensor are not tested here:
#  they already hold syntactically in Syn, see the systematic section)
Check( "id_x (x) id_y = id_xy", IsEqualForMorphisms( TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), IdentityMorphism( Ob( [2,1] ) ) ), IdentityMorphism( Ob( [1,2,1] ) ) ) );
Check( "interchange law (1)",
       IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( f, IdentityMorphism( Source( g ) ) ), TensorProductOnMorphisms( IdentityMorphism( Target( f ) ), g ) ), TensorProductOnMorphisms( f, g ) ) );
Check( "interchange law (2)",
       IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( IdentityMorphism( Source( f ) ), g ), TensorProductOnMorphisms( f, IdentityMorphism( Target( g ) ) ) ), TensorProductOnMorphisms( f, g ) ) );
Check( "interchange law: (id_ss (x) merge) ; (merge (x) id_s) = merge (x) merge",
       IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( IdentityMorphism( Ob( [1,1] ) ), merge1 ), TensorProductOnMorphisms( merge1, IdentityMorphism( Ob( [1] ) ) ) ), TensorProductOnMorphisms( merge1, merge1 ) ) );
a1 := split1;  b1 := merge1;  a2 := LowerDot( D, 2 );  b2 := UpperDot( D, 2 );
Check( "functoriality of the tensor",
       IsEqualForMorphisms( TensorProductOnMorphisms( PreCompose( a1, b1 ), PreCompose( a2, b2 ) ),
            PreCompose( TensorProductOnMorphisms( a1, a2 ), TensorProductOnMorphisms( b1, b2 ) ) ) );
# lowerdot (x) id_s and id_s (x) lowerdot are parallel ([1,1] -> [1]): they differ only in the order, not trivially in source/target
Check( "lowerdot (x) id_s and id_s (x) lowerdot are parallel",
       IsEqualForObjects( Source( TensorProductOnMorphisms( lowerdot, IdentityMorphism( Ob( [ 1 ] ) ) ) ),
                          Source( TensorProductOnMorphisms( IdentityMorphism( Ob( [ 1 ] ) ), lowerdot ) ) ) and
       IsEqualForObjects( Target( TensorProductOnMorphisms( lowerdot, IdentityMorphism( Ob( [ 1 ] ) ) ) ),
                          Target( TensorProductOnMorphisms( IdentityMorphism( Ob( [ 1 ] ) ), lowerdot ) ) ) );
Check( "the tensor is not commutative",
       not IsEqualForMorphisms( TensorProductOnMorphisms( lowerdot, IdentityMorphism( Ob( [ 1 ] ) ) ),
                                TensorProductOnMorphisms( IdentityMorphism( Ob( [ 1 ] ) ), lowerdot ) ) );
Check( "zigzag (split (x) id) ; (id (x) merge) <> id_ss",
       not IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( split1, IdentityMorphism( Ob( [1] ) ) ), TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), merge1 ) ), IdentityMorphism( Ob( [1,1] ) ) ) );

# equality does not depend on the order of independent layers, the second is the canonical form of the first
Check( "MorphismConstructor: layers in another order give an equal morphism",
       IsEqualForMorphisms( MorphismConstructor( D, Ob( [1,1,1,1] ),
              [ [ 2, [1,1], [1], [ "TrivalentVertex", 1 ] ], [ 0, [1,1], [1], [ "TrivalentVertex", 1 ] ] ],
              Ob( [1,1] ) ),
            TensorProductOnMorphisms( merge1, merge1 ) ) );

# lazy normalization: BSLayers is stored as it comes, BSCanonicalLayers
# is computed only when needed
# (CAP caches the results of the operations: m0 must be a morphism never
#  built before, otherwise it could be an old object already normalized)
m0 := TensorProductOnMorphisms( SplitVertex( D, 2 ), MergeVertex( D, 2 ) );
Check( "lazy: the canonical form is not computed at construction", not HasBSCanonicalLayers( m0 ) );
m1 := PreCompose( TensorProductOnMorphisms( merge1, IdentityMorphism( Ob( [1,1] ) ) ), TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), merge1 ) );   # (f (x) id) ; (id (x) g)
m2 := PreCompose( TensorProductOnMorphisms( IdentityMorphism( Ob( [1,1] ) ), merge1 ), TensorProductOnMorphisms( merge1, IdentityMorphism( Ob( [1] ) ) ) );   # (id (x) g) ; (f (x) id)
Check( "(merge (x) id) ; (id (x) merge) = (id (x) merge) ; (merge (x) id)", IsEqualForMorphisms( m1, m2 ) );
Check( "m1, m2 have different BSLayers", BSLayers( m1 ) <> BSLayers( m2 ) );
Check( "m1, m2 have the same BSCanonicalLayers", BSCanonicalLayers( m1 ) = BSCanonicalLayers( m2 ) );
fst := spider12;  gs := LowerDot( D, 2 );                  # [1,2,1] -> [2,1,2],  [2] -> []
n1 := PreCompose( TensorProductOnMorphisms( fst, IdentityMorphism( Ob( [2] ) ) ), TensorProductOnMorphisms( IdentityMorphism( Target( fst ) ), gs ) );
n2 := PreCompose( TensorProductOnMorphisms( IdentityMorphism( Source( fst ) ), gs ), TensorProductOnMorphisms( fst, IdentityMorphism( TensorUnit( D ) ) ) );
Check( "(Spider (x) id) ; (id (x) LowerDot) = (id (x) LowerDot) ; (Spider (x) id)", IsEqualForMorphisms( n1, n2 ) );
Check( "n1, n2 have different BSLayers and the same BSCanonicalLayers",
       BSLayers( n1 ) <> BSLayers( n2 ) and BSCanonicalLayers( n1 ) = BSCanonicalLayers( n2 ) );
Check( "same generators in an order not allowed by the interchange law -> different",
       not IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( split1, IdentityMorphism( Ob( [1] ) ) ), TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), merge1 ) ),
                PreCompose( TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), split1 ), TensorProductOnMorphisms( merge1, IdentityMorphism( Ob( [1] ) ) ) ) ) );

# cases with empty parts (morphisms from/to the unit)
Check( "lowerdot (x) upperdot = upperdot o lowerdot", IsEqualForMorphisms( TensorProductOnMorphisms( lowerdot, upperdot ), PreCompose( lowerdot, upperdot ) ) );
Check( "upperdot (x) lowerdot = upperdot o lowerdot", IsEqualForMorphisms( TensorProductOnMorphisms( upperdot, lowerdot ), PreCompose( lowerdot, upperdot ) ) );
Check( "upperdot o lowerdot <> id_s", not IsEqualForMorphisms( PreCompose( lowerdot, upperdot ), IdentityMorphism( Ob( [1] ) ) ) );
barbell := PreCompose( upperdot, lowerdot );   # endomorphism of the unit
Check( "scalar <> id of the unit", not IsEqualForMorphisms( barbell, IdentityMorphism( TensorUnit( D ) ) ) );
Check( "scalar on the left <> on the right of a strand (no braiding)",
       not IsEqualForMorphisms( TensorProductOnMorphisms( barbell, IdentityMorphism( Ob( [1] ) ) ), TensorProductOnMorphisms( IdentityMorphism( Ob( [1] ) ), barbell ) ) );
Check( "scalars: barbell (x) barbell = barbell o barbell", IsEqualForMorphisms( TensorProductOnMorphisms( barbell, barbell ), PreCompose( barbell, barbell ) ) );

# in Syn (purely syntactic equality) composition is NOT
# associative: the two trees are different. This test documents the fact.
Syn := ModelingCategory( D );
mf := ModelingMorphism( D, f );  mg := ModelingMorphism( D, g );  mh := ModelingMorphism( D, h );
Check( "in Syn (f g) h and f (g h) are different terms",
       not IsEqualForMorphisms( Syn, PreCompose( Syn, PreCompose( Syn, mf, mg ), mh ),
                                     PreCompose( Syn, mf, PreCompose( Syn, mg, mh ) ) ) );

# canonical form directly
Check( "FreeBSCanonicalLayers idempotent",
       FreeBSCanonicalLayers( BSCanonicalLayers( TensorProductOnMorphisms( f, g ) ) ) = BSCanonicalLayers( TensorProductOnMorphisms( f, g ) ) );

# ---------- systematic check of the axioms of strict monoidal category ----------
# The axioms are checked on small families of morphisms and on ALL the
# composable/tensorable tuples of them.
# Since the category is strict, associators and unitors are identities
# (CAP does not even provide them for D): pentagon and triangle are trivial.
# The essential point is that equality is NOT syntactic (interchange law),
# so we also check that it is an equivalence relation compatible with
# PreCompose and TensorProductOnMorphisms (congruence).
#
# NOT tested in D: the axioms that already hold syntactically in Syn (Syn
# flattens the tensor products): associativity and unit of the tensor (on
# objects and on morphisms), identity laws, source/target of identities,
# compositions and tensor products. Equal terms of Syn give the same layers
# in D, so these tests would check nothing new; the assumption itself is
# checked once, directly in Syn, below.
#
# Running time: every PreCompose / TensorProductOnMorphisms goes D -> Syn -> D
# (one Syn morphism per layer), so it costs milliseconds and grows with the
# number of layers; the canonical form is negligible here. Hence the families
# are small: the tuples of a Cartesian product all run the same code, what
# matters is to cover the edge cases (unit, empty source/target, identities,
# long words, independent layers).
CheckAll := function( name, tuples, pred )
  local bad;
  bad := First( tuples, t -> not CallFuncList( pred, t ) );
  Check( Concatenation( name, " (", String( Length( tuples ) ), " cases)" ), bad = fail );
  if bad <> fail then Print( "   counterexample: ", List( bad, x -> [ SourceTargetWords( x ), BSLayers( x ) ] ), "\n" ); fi;
end;
I := TensorUnit( D );
objs := List( [ [], [1], [2], [1,2], [2,1,1] ], Ob );
# sample: the generators of colour 1 (dots: empty target/source; trivalent
# vertices), a Spider (long word), identities of the unit and of a word,
# an endomorphism of the unit, a composite with two independent layers
sample := Concatenation( gens{[ 1 .. 4 ]},
  [ spider12, IdentityMorphism( I ), IdentityMorphism( Ob( [1] ) ), barbell, m1 ] );
small := [ lowerdot, merge1, spider12, barbell, IdentityMorphism( I ) ];
Composable := { a, b } -> IsEqualForObjects( Target( a ), Source( b ) );
pairs  := Cartesian( sample, sample );
cpairs := Filtered( pairs, p -> Composable( p[1], p[2] ) );
ctriples := Concatenation( List( cpairs, p -> List( Filtered( sample, c -> Composable( p[2], c ) ),
                                                     c -> [ p[1], p[2], c ] ) ) );
Check( "there are enough composable triples", Length( ctriples ) >= 20 );

# well-definedness: the layers fit the source and end in the target
CheckAll( "well-defined objects", List( objs, o -> [ o ] ), IsWellDefinedForObjects );
CheckAll( "well-defined (sample)", List( sample, m -> [ m ] ), IsWellDefinedForMorphisms );
CheckAll( "well-defined (compositions)", cpairs, { a, b } -> IsWellDefinedForMorphisms( PreCompose( a, b ) ) );
CheckAll( "well-defined (tensor products)", Cartesian( small, small ), { a, b } -> IsWellDefinedForMorphisms( TensorProductOnMorphisms( a, b ) ) );
Check( "IsWellDefined (generic CAP dispatcher) on an object and a morphism",
       IsWellDefined( Ob( [1,2] ) ) and IsWellDefined( spider12 ) );
# ill-defined cells, built bypassing the constructors (which would raise an error)
BadO := w -> CreateCapCategoryObjectWithAttributes( D, BSUnderlyingWord, w );
BadM := { S, layers, T } -> CreateCapCategoryMorphismWithAttributes( D, S, T, BSLayers, layers );
Check( "ill-defined object: letter out of range", not IsWellDefinedForObjects( BadO( [ 3 ] ) ) );
Check( "ill-defined object: not a list of integers", not IsWellDefinedForObjects( BadO( [ "s" ] ) ) );
Check( "ill-defined morphism: layer that does not fit the source",
       not IsWellDefinedForMorphisms( BadM( Ob( [2] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: invalid generator",
       not IsWellDefinedForMorphisms( BadM( Ob( [1] ), [ [ 0, [1], [], [ "TrivalentVertex", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: unknown label",
       not IsWellDefinedForMorphisms( BadM( Ob( [1] ), [ [ 0, [1], [], [ "Foo", 1 ] ] ], I ) ) );
Check( "ill-defined morphism: wrong target",
       not IsWellDefinedForMorphisms( BadM( Ob( [1] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], Ob( [1] ) ) ) );
Check( "ill-defined morphism: malformed layer", not IsWellDefinedForMorphisms( BadM( Ob( [1] ), [ [ 0, [1] ] ], I ) ) );
Check( "ill-defined morphism: ill-defined source",
       not IsWellDefinedForMorphisms( BadM( BadO( [ 3 ] ), [ ], BadO( [ 3 ] ) ) ) );

# the axioms omitted in D hold syntactically in Syn (checked once here)
Check( "in Syn: associativity and unit of the tensor, identity law hold syntactically",
       IsEqualForMorphisms( Syn, TensorProductOnMorphisms( Syn, TensorProductOnMorphisms( Syn, mf, mg ), mh ),
                                 TensorProductOnMorphisms( Syn, mf, TensorProductOnMorphisms( Syn, mg, mh ) ) ) and
       IsEqualForMorphisms( Syn, TensorProductOnMorphisms( Syn, IdentityMorphism( Syn, TensorUnit( Syn ) ), mf ), mf ) and
       IsEqualForMorphisms( Syn, TensorProductOnMorphisms( Syn, mf, IdentityMorphism( Syn, TensorUnit( Syn ) ) ), mf ) and
       IsEqualForMorphisms( Syn, PreCompose( Syn, IdentityMorphism( Syn, Source( mf ) ), mf ), mf ) );

# category: associativity of composition (NOT syntactic in Syn)
CheckAll( "associativity of composition", ctriples,
          { a, b, c } -> IsEqualForMorphisms( PreCompose( PreCompose( a, b ), c ), PreCompose( a, PreCompose( b, c ) ) ) );

# tensor is a bifunctor
CheckAll( "id_a (x) id_b = id_(a (x) b)", Cartesian( objs, objs ),
          { a, b } -> IsEqualForMorphisms( TensorProductOnMorphisms( IdentityMorphism( a ), IdentityMorphism( b ) ), IdentityMorphism( TensorProductOnObjects( a, b ) ) ) );
# composable pairs: dots, trivalent vertices, Spiders, identities of the unit
cpairs_small := [ [ upperdot, lowerdot ], [ split1, merge1 ], [ spider12, spider21 ],
                  [ IdentityMorphism( I ), IdentityMorphism( I ) ] ];
CheckAll( "functoriality: (a1 a2) (x) (b1 b2) = (a1 (x) b1)(a2 (x) b2)",
          List( Cartesian( cpairs_small, cpairs_small ), q -> Concatenation( q[1], q[2] ) ),
          { a1, a2, b1, b2 } -> IsEqualForMorphisms( TensorProductOnMorphisms( PreCompose( a1, a2 ), PreCompose( b1, b2 ) ),
                                     PreCompose( TensorProductOnMorphisms( a1, b1 ), TensorProductOnMorphisms( a2, b2 ) ) ) );
CheckAll( "interchange: (a (x) id)(id (x) b) = a (x) b = (id (x) b)(a (x) id)", Cartesian( small, small ),
          { a, b } -> IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( a, IdentityMorphism( Source( b ) ) ), TensorProductOnMorphisms( IdentityMorphism( Target( a ) ), b ) ), TensorProductOnMorphisms( a, b ) ) and
                      IsEqualForMorphisms( PreCompose( TensorProductOnMorphisms( IdentityMorphism( Source( a ) ), b ), TensorProductOnMorphisms( a, IdentityMorphism( Target( b ) ) ) ), TensorProductOnMorphisms( a, b ) ) );

# equality: equivalence relation and congruence
CheckAll( "equality is reflexive", List( sample, m -> [ m ] ), m -> IsEqualForMorphisms( m, m ) );
CheckAll( "equality is symmetric", Filtered( pairs, p -> IsEqualForObjects( Source( p[1] ), Source( p[2] ) ) and
                                                      IsEqualForObjects( Target( p[1] ), Target( p[2] ) ) ),
          { a, b } -> IsEqualForMorphisms( a, b ) = IsEqualForMorphisms( b, a ) );
# three different representatives of dot (x) dot (x) dot : [1,1,1] -> []
# (with 2 layers there are only 2 orders: 3 independent layers are needed)
dl := p -> [ p, [1], [], [ "Dot", 1 ] ];
r1 := TensorProductOnMorphisms( TensorProductOnMorphisms( lowerdot, lowerdot ), lowerdot );                                       # left, middle, right
r2 := MorphismConstructor( D, Ob( [1,1,1] ), [ dl( 2 ), dl( 1 ), dl( 0 ) ], I ); # right, middle, left
r3 := MorphismConstructor( D, Ob( [1,1,1] ), [ dl( 1 ), dl( 0 ), dl( 0 ) ], I ); # middle, left, right
Check( "three distinct representatives", Length( Set( [ BSLayers( r1 ), BSLayers( r2 ), BSLayers( r3 ) ] ) ) = 3 );
Check( "equality is transitive (r1 = r2, r2 = r3, r1 = r3)", IsEqualForMorphisms( r1, r2 ) and IsEqualForMorphisms( r2, r3 ) and IsEqualForMorphisms( r1, r3 ) );
# equal morphisms with different layers stay equal after o and (x)
q1 := TensorProductOnMorphisms( merge1, merge1 );
q2 := PreCompose( TensorProductOnMorphisms( IdentityMorphism( Ob( [1,1] ) ), merge1 ), TensorProductOnMorphisms( merge1, IdentityMorphism( Ob( [1] ) ) ) );
Check( "q1, q2 have different layers", BSLayers( q1 ) <> BSLayers( q2 ) );
reps := [ [ q1, q2 ], [ r1, r2 ], [ r2, r3 ], [ m1, m2 ], [ n1, n2 ] ];
# morphisms that end in the sources of the representatives
into := Concatenation( sample, [ TensorProductOnMorphisms( split1, split1 ),                        # [1,1] -> [1,1,1,1]
                                 TensorProductOnMorphisms( split1, IdentityMorphism( Ob( [1] ) ) ),           # [1,1] -> [1,1,1]
                                 TensorProductOnMorphisms( spider21, UpperDot( D, 2 ) ) ] );     # [2,1,2] -> [1,2,1,2]
CheckAll( "congruence for PreCompose (on the right)",
          Concatenation( List( reps, p -> List( Filtered( sample, c -> Composable( p[1], c ) ), c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> IsEqualForMorphisms( PreCompose( a, c ), PreCompose( b, c ) ) );
CheckAll( "congruence for PreCompose (on the left)",
          Concatenation( List( reps, p -> List( Filtered( into, c -> Composable( c, p[1] ) ), c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> IsEqualForMorphisms( PreCompose( c, a ), PreCompose( c, b ) ) );
CheckAll( "congruence for the tensor (both sides)",
          Concatenation( List( reps, p -> List( small, c -> [ p[1], p[2], c ] ) ) ),
          { a, b, c } -> IsEqualForMorphisms( TensorProductOnMorphisms( a, c ), TensorProductOnMorphisms( b, c ) ) and IsEqualForMorphisms( TensorProductOnMorphisms( c, a ), TensorProductOnMorphisms( c, b ) ) );

# infinite groups
W3 := CoxeterGroupByMatrix( [[1,3,3],[3,1,3],[3,3,1]] );
D3 := FreeBSCategory( W3 );
Check( "affine A2~: 4*3 + 6 = 18 generators", Length( BSGeneratingMorphisms( D3 ) ) = 18 );
Winf := CoxeterGroupByMatrix( [[1,infinity],[infinity,1]] );
Dinf := FreeBSCategory( Winf );
Check( "m = infinity: the category exists, 8 generators (no Spider)",
       Length( BSGeneratingMorphisms( Dinf ) ) = 8 );

# errors
CheckErr( "Spider with s = t -> error", { } -> SpiderMorphism( D, 1, 1 ),
          "a Spider needs two distinct colours" );
CheckErr( "Spider with m = infinity -> error", { } -> SpiderMorphism( Dinf, 1, 2 ),
          "m_st <> infinity" );
CheckErr( "unknown label -> error", { } -> BSGeneratingMorphism( D, [1], [ "Foo", 1 ], [] ),
          "unknown label" );
CheckErr( "Dot with wrong source/target -> error", { } -> BSGeneratingMorphism( D, [1], [ "Dot", 1 ], [1] ),
          "a Dot of colour 1 goes" );
CheckErr( "Spider in the wrong direction -> error",
          { } -> BSGeneratingMorphism( D, [1,2,1], [ "Spider", 2, 1 ], [2,1,2] ),
          "a Spider [ \"Spider\", 2, 1 ] goes" );
CheckErr( "letter out of range -> error", { } -> BSObject( D, [ 3 ] ),
          "the word must be a list of integers in [1..2]" );
CheckErr( "MorphismConstructor with an invalid layer -> error",
          { } -> MorphismConstructor( D, Ob( [1] ), [ [ 0, [1], [], [ "TrivalentVertex", 1 ] ] ], Ob( [] ) ),
          "a TrivalentVertex of colour 1 goes" );
CheckErr( "MorphismConstructor with a wrong target -> error",
          { } -> MorphismConstructor( D, Ob( [1] ), [ [ 0, [1], [], [ "Dot", 1 ] ] ], Ob( [1] ) ),
          "the layers do not end in the target word" );

Print( "\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " tests passed" );
if TEST_FAILED = 0 then Print( " -- ALL OK\n" ); else Print( " -- ", TEST_FAILED, " FAILED\n" ); fi;
QUIT;
