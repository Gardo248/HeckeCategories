#############################################################
# FreeBSCategory.gi -- IMPLEMENTATIONS
#
# The CAP category FreeBSCategory( W ). The combinatorics of words
# (inversion sets, normal forms, subexpressions, indices of the
# double leaves) is in coxeter.gi.
#
# Tower:  FreeBSCategory( W )  =  ReinterpretationOfCategory( Syn ),
#         Syn = SyntacticCategoryInDoctrines( "IsStrictMonoidalCategory" ).
#
# In Syn:
#   generator s_i     : ObjectConstructor( Syn, Pair( "ObjectConstructor", [ Syn, name_i ] ) )
#   word x            : TensorProductOnListOfObjects( Syn, [ generators ] )
#                       (also for |x| <= 1: it is the form that Syn itself
#                        produces when flattening the tensors)
#   generating mor.   : MorphismConstructor( Syn, x, Pair( "MorphismConstructor",
#                                            [ Syn, "Dot_1" ] ), y )
#                       (names "Dot_s", "TrivalentVertex_s", "Spider_s_t", see
#                        FreeBS_GeneratorName; source and target fix the direction)
#   layer [p,...]     : TensorProductOnListOfMorphisms( Syn, [ id_left, gen, id_right ] )
#   morphism          : composition (PreCompose) of the layers
#
# Back from Syn: the syntactic term is read recursively and turned into a list of layers, stored as it is (the canonical form is computed just when it is strictly necessary, see BSCanonicalLayers).
#############################################################

#############################################################
# Why morphisms are stored as LAYERS
#
# A morphism is a list of layers [ p, x, y, label ], read in
# composition order; the layer [ p, x, y, label ] stands for
#     id_(p letters on the left) (x) gen(x -> y, label) (x) id_(rest).
#
# (1) Identities as wires are unavoidable, but are not stored.
#     Most morphisms cannot be written with (x) and o of the
#     generators alone, e.g. the zigzag
#         ( split (x) id_s ) o ( id_s (x) merge ) : ss -> sss -> ss
#     is neither a tensor product (the two vertices share a strand)
#     nor a composition of two generators. In a layer the identity
#     wires are encoded only by the integer p (the wires on the right
#     are determined by the word).
#
# (2) Most of the relations are quotiented out for free.
#     A syntactic term (a tree of (x) and o, as in Syn) has many
#     representatives of the same morphism: associativity of o and
#     of (x), unit laws, functoriality
#         ( f o g ) (x) ( h o k ) = ( f (x) h ) o ( g (x) k ).
#     Flattening the term into a list of layers kills all of them;
#     the only relation left is the INTERCHANGE LAW: two adjacent
#     layers acting on disjoint strands can be swapped (adjusting p),
#     e.g.
#         ( id_ss (x) merge ) o ( merge (x) id_s ) = merge (x) merge.
#     This relation is a property of the category, not of the
#     implementation: every implementation has to decide it.
#
# (3) Equality is decidable.
#     Two terms denote the same morphism of the free strict monoidal
#     category if and only if their lists of layers are related by
#     interchange moves (Joyal-Street; Delpeuch-Vicary, "Normalization
#     for planar string diagrams", 2018). Choosing a canonical
#     representative (FreeBSCanonicalLayers: lexicographic minimum)
#     reduces equality of morphisms to equality of lists.
#
# (4) The categorical operations are trivial.
#     Composition = concatenation of the lists; tensor product =
#     shift of the offsets p of the right factor and concatenation.
#
# (5) Useful for the future.
#     A monoidal functor (e.g. to Soergel bimodules) is evaluated layer
#     by layer from the images of the generators; the generators
#     occurring in a morphism are listed directly.

# ---------- canonical form (interchange law) ----------
#
# Layer l = [ p, x, y, label ]: it acts on the word u replacing
# u{[p+1..p+|x|]} = x with y. Two consecutive layers l1, l2 (l1 first)
# can be swapped if l2 acts entirely to the left
# (p2 + |x2| <= p1) or entirely to the right (p2 >= p1 + |y1|) of the
# output of l1. If both hold (|x2| = |y1| = 0, p1 = p2) both swaps are
# generated: the two diagrams are isotopic.
# The equivalence class is finite (same number of layers, bounded
# positions); its lexicographic minimum is returned.
# Cost: proportional to the size of the class (for k independent
# layers up to k!). Fine for now; in the future it can be
# replaced with the quadratic algorithm of Delpeuch-Vicary.
InstallGlobalFunction( FreeBSCanonicalLayers,
function( layers )
  local swaps, seen, todo, seq, new;

  swaps := function( seq )
    local res, i, l1, l2, p1, a1, b1, p2, a2, b2, s;
    res := [ ];
    for i in [ 1 .. Length( seq ) - 1 ] do
      l1 := seq[i];  l2 := seq[i+1];
      p1 := l1[1];  a1 := Length( l1[2] );  b1 := Length( l1[3] );
      p2 := l2[1];  a2 := Length( l2[2] );  b2 := Length( l2[3] );
      if p2 + a2 <= p1 then
        # l2 on the left: first l2 (same position), then l1 shifted
        s := ShallowCopy( seq );
        s[i]   := l2;
        s[i+1] := Concatenation( [ p1 - a2 + b2 ], l1{[ 2 .. 4 ]} );
        Add( res, s );
      fi;
      if p2 >= p1 + b1 then
        # l2 on the right: first l2 shifted, then l1 (same position)
        s := ShallowCopy( seq );
        s[i]   := Concatenation( [ p2 - b1 + a1 ], l2{[ 2 .. 4 ]} );
        s[i+1] := l1;
        Add( res, s );
      fi;
    od;
    return res;
  end;

  #search on the graph of isotopic diagrams (diagrams connected by a single swap of layers, found by swaps). AddSet keeps the list seen lexicographically sorted. todo stores the nodes of the graph still to be visited.
  seen := Set( [ layers ] );
  todo := [ layers ];
  while not IsEmpty( todo ) do
    seq := Remove( todo );
    for new in swaps( seq ) do
      if not new in seen then
        AddSet( seen, new );
        Add( todo, new );
      fi;
    od;
  od;
  return seen[1];
end );

# ---------- generating morphisms ----------

# the alternating word [ s, t, s, ... ] of length m
BindGlobal( "FreeBS_AlternatingWord",
function( s, t, m )
  local w, k;
  w := [ ];
  for k in [ 1 .. m ] do
    if IsOddInt( k ) then
      Add( w, s );
    else
      Add( w, t );
    fi;
  od;
  return w;
end );

# Checks that x -> y with the given label is a generating morphism:
#   [ "Dot", s ]             : [s] -> [] or [] -> [s]
#   [ "TrivalentVertex", s ] : [s,s] -> [s] or [s] -> [s,s]
#   [ "Spider", s, t ]       : [s,t,s,...] -> [t,s,t,...] (length m_st),
#                              only for s <> t and m_st <> infinity
BindGlobal( "FreeBS_CheckGenerator",
function( W, x, y, label )
  local M, n, s, t, m;
  M := CoxeterMatrix( W );
  n := Length( M );
  if not ( IsList( label ) and Length( label ) >= 2 and IsString( label[1] ) and
           ForAll( label{[ 2 .. Length( label ) ]}, i -> IsPosInt( i ) and i <= n ) ) then
    Error( "a label must be [ name, s ] or [ name, s, t ] with s, t in [1..", n, "]" );
  fi;
  s := label[2];
  if label[1] = "Dot" and Length( label ) = 2 then
    if not [ x, y ] in [ [ [ s ], [ ] ], [ [ ], [ s ] ] ] then
      Error( "a Dot of colour ", s, " goes [ ", s, " ] -> [ ] or [ ] -> [ ", s, " ]" );
    fi;
  elif label[1] = "TrivalentVertex" and Length( label ) = 2 then
    if not [ x, y ] in [ [ [ s, s ], [ s ] ], [ [ s ], [ s, s ] ] ] then
      Error( "a TrivalentVertex of colour ", s, " goes [ ", s, ", ", s, " ] -> [ ", s,
             " ] or [ ", s, " ] -> [ ", s, ", ", s, " ]" );
    fi;
  elif label[1] = "Spider" and Length( label ) = 3 then
    t := label[3];
    if s = t then
      Error( "a Spider needs two distinct colours" );
    fi;
    m := M[s][t];
    if m = infinity then
      Error( "there is no Spider for m_st = infinity" );
    fi;
    if x <> FreeBS_AlternatingWord( s, t, m ) or y <> FreeBS_AlternatingWord( t, s, m ) then
      Error( "a Spider [ \"Spider\", ", s, ", ", t, " ] goes ",
             FreeBS_AlternatingWord( s, t, m ), " -> ", FreeBS_AlternatingWord( t, s, m ) );
    fi;
  else
    Error( "unknown label ", label, " (allowed: \"Dot\", \"TrivalentVertex\", \"Spider\")" );
  fi;
end );

# Checks that the layers form a morphism u -> v
BindGlobal( "FreeBS_CheckLayers",
function( W, u, layers, v )
  local l, p, x, y;
  for l in layers do
    if not ( IsList( l ) and Length( l ) = 4 ) then
      Error( "a layer must be a list [ p, x, y, label ]" );
    fi;
    p := l[1];  x := l[2];  y := l[3];
    if not IsInt( p ) or p < 0 or p + Length( x ) > Length( u ) or
       u{[ p + 1 .. p + Length( x ) ]} <> x then
      Error( "the layer ", l, " does not fit the word ", u );
    fi;
    FreeBS_CheckGenerator( W, x, y, l[4] );
    u := Concatenation( u{[ 1 .. p ]}, y, u{[ p + Length( x ) + 1 .. Length( u ) ]} );
  od;
  if u <> v then
    Error( "the layers do not end in the target word" );
  fi;
end );

# ---------- names of the generating morphisms in Syn ----------
# [ "Dot", 1 ] <-> "Dot_1",  [ "Spider", 1, 2 ] <-> "Spider_1_2"
BindGlobal( "FreeBS_GeneratorName",
function( label )
  local parts;
  parts := Concatenation( [ label[1] ], List( label{[ 2 .. Length( label ) ]}, String ) );
  return JoinStringsWithSeparator( parts, "_" );
end );

BindGlobal( "FreeBS_LabelOfName",
function( name )
  local parts;
  parts := SplitString( name, "_" );
  return Concatenation( [ parts[1] ], List( parts{[ 2 .. Length( parts ) ]}, Int ) );
end );

# ---------- canonical form ----------
InstallMethod( BSCanonicalLayers,
  "for a morphism in a free BS category",
  [ IsMorphismInFreeBSCategory ],
  mor -> FreeBSCanonicalLayers( BSLayers( mor ) ) );

# ---------- the category ----------
InstallMethod( FreeBSCategory,
  "for a Coxeter group",
  [ IsCoxeterGroup ],
function( W )
  local M, names, Syn, gen_obj, word_to_syn, syn_to_word, tensor_layers, syn_mor_to_layers, layers_to_syn, is_equal_morphisms,
  # variables for the record ReinterpretationOfCategory:
        name, object_constructor, object_datum, morphism_constructor, morphism_datum,
        modeling_tower_object_constructor, modeling_tower_object_datum,
        modeling_tower_morphism_constructor, modeling_tower_morphism_datum, D;

  M := CoxeterMatrix( W );
  names := CoxeterGeneratorNames( W );

  Syn := SyntacticCategoryInDoctrines( "IsStrictMonoidalCategory" :
           with_given := true,
           name := Concatenation( "Syn( FreeBSCategory( ", String( M ), " ) )" ) );

  # words <-> objects of Syn
  # same list as "names" but now the elements are objects of Syn
  gen_obj := List( names, nm ->
               #same as nm / Syn but with a more explicit codification
               ObjectConstructor( Syn, Pair( "ObjectConstructor", [ Syn, nm ] ) ) );

  # x is always a list of integers in [1..length(names)]
  word_to_syn := x -> TensorProductOnListOfObjects( Syn, gen_obj{ x } );

  syn_to_word := function( obj )
    local d;
    d := ObjectDatum( Syn, obj );
    if d[1] = "ObjectConstructor" then
      return [ Position( names, d[2][2] ) ];
    elif d[1] = "TensorProductOnListOfObjects" then
      return Concatenation( List( d[2][2], syn_to_word ) );
    elif d[1] = "TensorProductOnObjects" then
      return Concatenation( syn_to_word( d[2][2] ), syn_to_word( d[2][3] ) );
    elif d[1] = "TensorUnit" then
      return [ ];
    fi;
    Error( "FreeBSCategory: unexpected syntactic object ", d[1] );
  end;

  ## tensor of factors [ source word, target word, layers ]:
  ## factor k acts after the factors on its left, which have
  ## already reached their target
  tensor_layers := function( factors )
    local res, offset, fac;
    res := [ ];
    offset := 0;
    for fac in factors do
      Append( res, List( fac[3], l -> Concatenation( [ l[1] + offset ], l{[ 2 .. 4 ]} ) ) );
      offset := offset + Length( fac[2] );
    od;
    return res;
  end;

  ## morphism of Syn -> list of layers (not yet canonical)
  syn_mor_to_layers := function( phi )
    local d, op, args, L, rest, factors;
    d := MorphismDatum( Syn, phi );
    op := d[1];
    args := d[2];
    if op = "MorphismConstructor" then
      # the name carries the label, source and target the direction
      return [ [ 0, syn_to_word( Source( phi ) ), syn_to_word( Range( phi ) ),
                 FreeBS_LabelOfName( args[2] ) ] ];
    elif op = "IdentityMorphism" then
      return [ ];
    elif op = "PreCompose" then
      return Concatenation( syn_mor_to_layers( args[2] ), syn_mor_to_layers( args[3] ) );
    elif op = "PostCompose" then
      return Concatenation( syn_mor_to_layers( args[3] ), syn_mor_to_layers( args[2] ) );
    elif op = "PreComposeList" then
      L := First( args, IsList );
      return Concatenation( List( L, syn_mor_to_layers ) );
    elif op = "PostComposeList" then
      L := First( args, IsList );
      return Concatenation( List( Reversed( L ), syn_mor_to_layers ) );
    elif StartsWith( op, "TensorProductOn" ) then
      rest := args{[ 2 .. Length( args ) ]};
      if EndsWith( op, "WithGivenTensorProducts" ) then
        rest := rest{[ 2 .. Length( rest ) - 1 ]};
      fi;
      if Length( rest ) = 1 and IsList( rest[1] ) then
        rest := rest[1];
      fi;
      factors := List( rest, function( c )
                   local w;
                   if IsCapCategoryMorphism( c ) then
                     return [ syn_to_word( Source( c ) ), syn_to_word( Range( c ) ),
                              syn_mor_to_layers( c ) ];
                   fi;
                   w := syn_to_word( c );
                   return [ w, w, [ ] ];
                 end );
      return tensor_layers( factors );
    fi;
    Error( "FreeBSCategory: unexpected syntactic morphism ", op );
  end;

  ## (source word, layers) -> [ morphism of Syn, target word ]
  ## (the layers have already been checked by FreeBS_CheckLayers)
  layers_to_syn := function( u, layers )
    local mor, l, p, x, y, left, right, gen, layer;
    mor := IdentityMorphism( Syn, word_to_syn( u ) );
    for l in layers do
      p := l[1];  x := l[2];  y := l[3];
      left  := u{[ 1 .. p ]};
      right := u{[ p + Length( x ) + 1 .. Length( u ) ]};
      gen := MorphismConstructor( Syn, word_to_syn( x ),
               Pair( "MorphismConstructor", [ Syn, FreeBS_GeneratorName( l[4] ) ] ),
               word_to_syn( y ) );
      layer := TensorProductOnListOfMorphisms( Syn,
                 [ IdentityMorphism( Syn, word_to_syn( left ) ), gen,
                   IdentityMorphism( Syn, word_to_syn( right ) ) ] );
      mor := PreCompose( Syn, mor, layer );
      u := Concatenation( left, y, right );
    od;
    return [ mor, u ];
  end;

  ## equality of two parallel morphisms. Fast checks first; the canonical
  ## form is computed only if they are inconclusive. The interchange law
  ## preserves the number of layers and the multiset of the generators
  ## [ x, y, label ] (only the offsets p change).
  is_equal_morphisms := function( a, b )
    local la, lb;
    la := BSLayers( a );
    lb := BSLayers( b );
    if la = lb then
      return true;
    elif Length( la ) <> Length( lb ) then
      return false;
    elif Collected( List( la, l -> l{[ 2 .. 4 ]} ) ) <>
         Collected( List( lb, l -> l{[ 2 .. 4 ]} ) ) then
      return false;
    fi;
    return BSCanonicalLayers( a ) = BSCanonicalLayers( b );
  end;

  ## ---------- the fields of ReinterpretationOfCategory ----------

  name := Concatenation( "FreeBSCategory( ", String( M ), " )" );

  ## object of D with datum the word x
  object_constructor := function( D, x )
    return CreateCapCategoryObjectWithAttributes( D, BSWord, x );
  end;

  object_datum := { D, obj } -> BSWord( obj );

  ## morphism of D with datum the list of layers; the layers are checked
  ## and stored as they come: the canonical form is computed only when
  ## comparing (BSCanonicalLayers)
  morphism_constructor := function( D, S, layers, T )
    FreeBS_CheckLayers( W, BSWord( S ), layers, BSWord( T ) );
    return CreateCapCategoryMorphismWithAttributes( D, S, T, BSLayers, layers );
  end;

  morphism_datum := { D, mor } -> BSLayers( mor );

  ## word -> object of Syn
  modeling_tower_object_constructor := { D, x } -> word_to_syn( x );

  ## object of Syn -> word
  modeling_tower_object_datum := { D, obj } -> syn_to_word( obj );

  ## list of layers -> morphism of Syn (layers_to_syn also returns the
  ## target word, not needed here)
  modeling_tower_morphism_constructor := function( D, S, layers, T )
    local r;
    r := layers_to_syn( syn_to_word( S ), layers );
    return r[1];
  end;

  ## morphism of Syn -> list of layers
  modeling_tower_morphism_datum := { D, phi } -> syn_mor_to_layers( phi );

  ## The fields of the record are defined above as local variables and only
  ## listed here (style of FiniteCocompletions/FiniteStrictProductCompletion.gi).
  ## For the compact version, with the functions written inline inside this
  ## call, see the commit with tag "compact-reinterpretation-record"
  ## (git show compact-reinterpretation-record:FreeBSCategory.gi).
  D := ReinterpretationOfCategory( Syn, rec(
         name := name,
         category_filter := IsFreeBSCategory,
         category_object_filter := IsObjectInFreeBSCategory,
         category_morphism_filter := IsMorphismInFreeBSCategory,
         object_constructor := object_constructor,
         object_datum := object_datum,
         morphism_constructor := morphism_constructor,
         morphism_datum := morphism_datum,
         modeling_tower_object_constructor := modeling_tower_object_constructor,
         modeling_tower_object_datum := modeling_tower_object_datum,
         modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
         modeling_tower_morphism_datum := modeling_tower_morphism_datum,
         only_primitive_operations := true )
       : FinalizeCategory := false );

  SetUnderlyingCoxeterGroup( D, W );

  ## equalities: see is_equal_morphisms above
  ## (in Syn equality is only syntactic and IsCongruentForMorphisms
  ##  raises an error)
  ## (weight 1 < 50 = weight of the functions inherited from Syn, otherwise
  ##  CAP ignores these)
  AddIsEqualForObjects( D, { D, a, b } -> BSWord( a ) = BSWord( b ), 1 );
  AddIsEqualForMorphisms( D, { D, a, b } -> is_equal_morphisms( a, b ), 1 );
  AddIsCongruentForMorphisms( D, { D, a, b } -> is_equal_morphisms( a, b ), 1 );

  Finalize( D );
  return D;
end );

# ---------- convenience constructors ----------
InstallMethod( BSObject,
  "for a free BS category and a word",
  [ IsFreeBSCategory, IsList ],
function( D, x )
  CheckCoxeterWord( UnderlyingCoxeterGroup( D ), x );
  return ObjectConstructor( D, x );
end );

InstallMethod( BSGeneratingMorphism,
  "for a free BS category, a source word, a label and a target word",
  [ IsFreeBSCategory, IsList, IsList, IsList ],
function( D, x, label, y )
  return MorphismConstructor( D, BSObject( D, x ), [ [ 0, x, y, label ] ], BSObject( D, y ) );
end );

InstallMethod( StartDot,
  "for a free BS category and a colour",
  [ IsFreeBSCategory, IsPosInt ],
  { D, s } -> BSGeneratingMorphism( D, [ ], [ "Dot", s ], [ s ] ) );

InstallMethod( EndDot,
  "for a free BS category and a colour",
  [ IsFreeBSCategory, IsPosInt ],
  { D, s } -> BSGeneratingMorphism( D, [ s ], [ "Dot", s ], [ ] ) );

InstallMethod( SplitVertex,
  "for a free BS category and a colour",
  [ IsFreeBSCategory, IsPosInt ],
  { D, s } -> BSGeneratingMorphism( D, [ s ], [ "TrivalentVertex", s ], [ s, s ] ) );

InstallMethod( MergeVertex,
  "for a free BS category and a colour",
  [ IsFreeBSCategory, IsPosInt ],
  { D, s } -> BSGeneratingMorphism( D, [ s, s ], [ "TrivalentVertex", s ], [ s ] ) );

InstallMethod( SpiderMorphism,
  "for a free BS category and two colours",
  [ IsFreeBSCategory, IsPosInt, IsPosInt ],
function( D, s, t )
  local M, m;
  M := CoxeterMatrix( UnderlyingCoxeterGroup( D ) );
  if s = t or s > Length( M ) or t > Length( M ) or M[s][t] = infinity then
    Error( "a Spider needs two distinct colours s, t with m_st <> infinity" );
  fi;
  m := M[s][t];
  return BSGeneratingMorphism( D, FreeBS_AlternatingWord( s, t, m ), [ "Spider", s, t ],
                                  FreeBS_AlternatingWord( t, s, m ) );
end );

InstallMethod( BSGeneratingMorphisms,
  "for a free BS category",
  [ IsFreeBSCategory ],
function( D )
  local M, n, res, s, t;
  M := CoxeterMatrix( UnderlyingCoxeterGroup( D ) );
  n := Length( M );
  res := [ ];
  for s in [ 1 .. n ] do
    Append( res, [ StartDot( D, s ), EndDot( D, s ), SplitVertex( D, s ), MergeVertex( D, s ) ] );
  od;
  for s in [ 1 .. n ] do
    for t in [ 1 .. n ] do
      if s <> t and M[s][t] <> infinity then
        Add( res, SpiderMorphism( D, s, t ) );
      fi;
    od;
  od;
  return res;
end );
