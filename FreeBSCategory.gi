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
#   light leaf        : MorphismConstructor( Syn, x, Pair( "MorphismConstructor",
#                                            [ Syn, "LL[ x, y, e, f, w ]" ] ), y )
#   layer [p,...]     : TensorProductOnListOfMorphisms( Syn, [ id_left, LL, id_right ] )
#   morphism          : composition (PreCompose) of the layers
#
# Back from Syn: the syntactic term is read recursively and turned into a list of layers, then put in canonical form.
#############################################################

# ---------- light leaves that are identities ----------
# leaf = [ x, y, e, f, w ]: it is the identity of x if x = y and if e, f choose the whole expression.
BindGlobal( "FreeBS_IsIdentityLeaf",
  leaf -> leaf[1] = leaf[2] and ForAll( leaf[3], i -> i = 1 )
                            and ForAll( leaf[4], i -> i = 1 ) );

# ---------- canonical form (interchange law) ----------
#
# Layer l = [ p, x, y, e, f, w ]: it acts on the word u replacing
# u{[p+1..p+|x|]} = x with y. Two consecutive layers l1, l2 (l1 first)
# can be swapped if l2 acts entirely to the left
# (p2 + |x2| <= p1) or entirely to the right (p2 >= p1 + |y1|) of the
# output of l1. If both hold (|x2| = |y1| = 0, p1 = p2) both swaps are
# generated: the two diagrams are isotopic.
# First of all the layers that are identities are removed (see
# FreeBS_IsIdentityLeaf).
# The equivalence class is finite (same number of layers, bounded
# positions); its lexicographic minimum is returned.
# Cost: proportional to the size of the class (for k independent
# layers up to k!). Fine for now; in the future it can be
# replaced with the quadratic algorithm of Delpeuch-Vicary.
InstallGlobalFunction( FreeBSCanonicalLayers,
function( layers )
  local swaps, seen, todo, seq, new;

  # the light leaf with x = y and e = f = (1,...,1) is the identity of x:
  # the corresponding layer is removed
  layers := Filtered( layers, l -> not FreeBS_IsIdentityLeaf( l{[ 2 .. 6 ]} ) );

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
        s[i+1] := Concatenation( [ p1 - a2 + b2 ], l1{[ 2 .. 6 ]} );
        Add( res, s );
      fi;
      if p2 >= p1 + b1 then
        # l2 on the right: first l2 shifted, then l1 (same position)
        s := ShallowCopy( seq );
        s[i]   := Concatenation( [ p2 - b1 + a1 ], l2{[ 2 .. 6 ]} );
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

# ---------- names of the light leaves in Syn ----------
BindGlobal( "FreeBS_LeafName",
  leaf -> Concatenation( "LL", String( leaf ) ) );

BindGlobal( "FreeBS_LeafOfName",
  name -> EvalString( name{[ 3 .. Length( name ) ]} ) );

# ---------- checks ----------
BindGlobal( "FreeBS_CheckLeaf",
function( W, x, y, t )
  local e, f, w;
  CheckCoxeterWord( W, x );
  CheckCoxeterWord( W, y );
  if not ( IsList( t ) and Length( t ) = 3 ) then
    Error( "the index of a light leaf must be a triple [ e, f, w ]" );
  fi;
  e := t[1];  f := t[2];  w := t[3];
  if not ( IsList( e ) and Length( e ) = Length( x ) and ForAll( e, i -> i in [ 0, 1 ] ) ) then
    Error( "e must be a 0/1 list of the same length as the source word" );
  fi;
  if not ( IsList( f ) and Length( f ) = Length( y ) and ForAll( f, i -> i in [ 0, 1 ] ) ) then
    Error( "f must be a 0/1 list of the same length as the target word" );
  fi;
  CheckCoxeterWord( W, w );
  if CoxeterNormalFormOfWord( W, w ) <> w then
    Error( "w must be given in normal form" );
  fi;
  if CoxeterNormalFormOfWord( W, x{ Positions( e, 1 ) } ) <> w or
     CoxeterNormalFormOfWord( W, y{ Positions( f, 1 ) } ) <> w then
    Error( "the subexpressions e and f do not both end in w" );
  fi;
end );

# ---------- the category ----------
InstallMethod( FreeBSCategory,
  "for a Coxeter group",
  [ IsCoxeterGroup ],
function( W )
  local M, names, Syn, gen_obj, word_to_syn, syn_to_word, tensor_layers,
        syn_mor_to_layers, layers_to_syn, D;

  M := CoxeterMatrix( W );
  if ForAny( M, row -> infinity in row ) then
    Error( "Coxeter matrices with entries infinity are not supported (yet)" );
  fi;
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
      Append( res, List( fac[3], l -> Concatenation( [ l[1] + offset ], l{[ 2 .. 6 ]} ) ) );
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
      return [ Concatenation( [ 0 ], FreeBS_LeafOfName( args[2] ) ) ];
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
  layers_to_syn := function( u, layers )
    local mor, l, p, x, y, left, right, gen, layer;
    mor := IdentityMorphism( Syn, word_to_syn( u ) );
    for l in layers do
      p := l[1];  x := l[2];  y := l[3];
      if not IsInt( p ) or p < 0 or p + Length( x ) > Length( u ) or
         u{[ p + 1 .. p + Length( x ) ]} <> x then
        Error( "the layer ", l, " does not fit the word ", u );
      fi;
      left  := u{[ 1 .. p ]};
      right := u{[ p + Length( x ) + 1 .. Length( u ) ]};
      gen := MorphismConstructor( Syn, word_to_syn( x ),
               Pair( "MorphismConstructor", [ Syn, FreeBS_LeafName( l{[ 2 .. 6 ]} ) ] ),
               word_to_syn( y ) );
      layer := TensorProductOnListOfMorphisms( Syn,
                 [ IdentityMorphism( Syn, word_to_syn( left ) ), gen,
                   IdentityMorphism( Syn, word_to_syn( right ) ) ] );
      mor := PreCompose( Syn, mor, layer );
      u := Concatenation( left, y, right );
    od;
    return [ mor, u ];
  end;

  D := ReinterpretationOfCategory( Syn, rec(
         name := Concatenation( "FreeBSCategory( ", String( M ), " )" ),
         category_filter := IsFreeBSCategory,
         category_object_filter := IsObjectInFreeBSCategory,
         category_morphism_filter := IsMorphismInFreeBSCategory,
         object_constructor := { D, x } ->
             CreateCapCategoryObjectWithAttributes( D, BSWord, x ),
         object_datum := { D, obj } -> BSWord( obj ),
         morphism_constructor := { D, S, layers, T } ->
             CreateCapCategoryMorphismWithAttributes( D, S, T,
                 BSLayers, FreeBSCanonicalLayers( layers ) ),
         morphism_datum := { D, mor } -> BSLayers( mor ),
         modeling_tower_object_constructor := { D, x } -> word_to_syn( x ),
         modeling_tower_object_datum := { D, obj } -> syn_to_word( obj ),
         modeling_tower_morphism_constructor := function( D, S, layers, T )
             local r;
             r := layers_to_syn( syn_to_word( S ), layers );
             if r[2] <> syn_to_word( T ) then
               Error( "the layers do not end in the target word" );
             fi;
             return r[1];
           end,
         modeling_tower_morphism_datum := { D, phi } -> syn_mor_to_layers( phi ),
         only_primitive_operations := true )
       : FinalizeCategory := false );

  SetUnderlyingCoxeterGroup( D, W );

  ## equalities: the data are canonical, so comparing them is enough
  ## (in Syn equality is only syntactic and IsCongruentForMorphisms
  ##  raises an error)
  ## (weight 1 < 50 = weight of the functions inherited from Syn, otherwise
  ##  CAP ignores these)
  AddIsEqualForObjects( D, { D, a, b } -> BSWord( a ) = BSWord( b ), 1 );
  AddIsEqualForMorphisms( D, { D, a, b } -> BSLayers( a ) = BSLayers( b ), 1 );
  AddIsCongruentForMorphisms( D, { D, a, b } -> BSLayers( a ) = BSLayers( b ), 1 );

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

InstallMethod( LightLeafMorphism,
  "for a free BS category, two words and a triple [ e, f, w ]",
  [ IsFreeBSCategory, IsList, IsList, IsList ],
function( D, x, y, t )
  FreeBS_CheckLeaf( UnderlyingCoxeterGroup( D ), x, y, t );
  return MorphismConstructor( D, BSObject( D, x ),
           [ Concatenation( [ 0, x, y ], t ) ], BSObject( D, y ) );
end );

InstallMethod( LightLeafMorphisms,
  "for a free BS category and two words",
  [ IsFreeBSCategory, IsList, IsList ],
  { D, x, y } -> List( DoubleLeavesIndicesOfHom( UnderlyingCoxeterGroup( D ), x, y ),
                       t -> LightLeafMorphism( D, x, y, t ) ) );
