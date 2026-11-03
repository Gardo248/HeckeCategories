#############################################################
# FreeBSCategory.gi -- IMPLEMENTAZIONI
#
# Matematica (vedi la spiegazione allegata):
#   B = forma bilineare di Coxeter, esatta (CoxeterBilinearForm).
#   s_i agisce sui vettori di coordinate v = sum_j v_j alpha_j come
#       s_i(v) = v - 2 B(alpha_i, v) alpha_i,
#   cioe' cambia solo la coordinata i-esima:
#       v_i  ->  v_i - 2 * sum_j B[i][j] * v_j.
#   I(w) = { beta > 0 : w(beta) < 0 }.  Fatti (Tits, Humphreys 5.4-5.6):
#     (1) s_i e' descent destro di w  <=>  alpha_i in I(w);
#     (2) se alpha_i in I(w):  I(w s_i) = s_i( I(w) \ {alpha_i} );
#         altrimenti:          I(w s_i) = { alpha_i } u s_i( I(w) ).
#   Nessun confronto di segni: solo uguaglianza tra vettori esatti.
#############################################################

# riflessione s_i sul vettore v (coordinate nelle radici semplici)
BindGlobal( "ReflectionInGeomRepr",
function( B, i, v )
  local sv;
  sv := ShallowCopy( v );
  sv[i] := v[i] - 2 * Sum( [ 1 .. Length( v ) ], j -> B[i][j] * v[j] );
  return sv;
end );

#TODO: penso che questo sia superfluo, questo controllo va fatto in IsWellDefined
BindGlobal( "FreeBS_CheckWord",
function( G, x )
  local n;
  n := Length( CoxeterMatrix( G ) );
  if not ForAll( x, i -> IsPosInt( i ) and i <= n ) then
    Error( "the word must be a list of integers in [1..", n, "]" );
  fi;
end );

##
InstallMethod( InversionSetAfterRightMultiplication,
  "for a Coxeter group, an inversion set and a generator index",
  [ IsCoxeterGroup, IsList, IsPosInt ],
function( G, I, i )
  local B, n, alpha, J;
  B := CoxeterBilinearForm( G );
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
function( G, word )
  local I, i;
  FreeBS_CheckWord( G, word );
  I := [ ];
  for i in word do
    I := InversionSetAfterRightMultiplication( G, I, i );
  od;
  return I;
end );

##
InstallMethod( CoxeterNormalFormOfInversionSet,
  "for a Coxeter group and an inversion set",
  [ IsCoxeterGroup, IsList ],
function( G, I )
  local n, alphas, word, i, found;
  n := Length( CoxeterMatrix( G ) );
  alphas := IdentityMat( n );
  word := [ ];
  while not IsEmpty( I ) do
    found := false;
    for i in [ 1 .. n ] do
      if alphas[i] in I then
        # s_i e' il piu' piccolo descent destro: w = w' s_i
        Add( word, i );
        I := InversionSetAfterRightMultiplication( G, I, i );
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
  { G, word } -> CoxeterNormalFormOfInversionSet( G,
                   InversionSetOfCoxeterWord( G, word ) ) );

##
#the function uses a recursion to find all the subexpressions of a word, and, step by step, it computes the inversion set of the subexpression.
#Then it computes the normal form of the inversion set, just once for each inversion set. To do that it uses a cache key,
#which contains all the inversion sets whose normal form has already been computed, and a cache value, which contains the normal forms of the inversion sets in the cache key.
#The function returns a list of pairs [e, w], where e is a 0/1 list representing the subexpression and w is the normal form of the inversion set of that subexpression.
InstallMethod( SubexpressionsOfCoxeterWord,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
function( G, x )
  local n, leaves, cache_keys, cache_vals, walk, res, leaf, p;
  FreeBS_CheckWord( G, x );
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
    walk( k + 1, e, InversionSetAfterRightMultiplication( G, I, x[k] ) );
    Remove( e );
  end;
  walk( 1, [ ], [ ] );
  # la forma normale si calcola una sola volta per ogni insieme di inversioni
  cache_keys := [ ];
  cache_vals := [ ];
  res := [ ];
  for leaf in leaves do
    p := Position( cache_keys, leaf[2] );
    if p = fail then
      Add( cache_keys, leaf[2] );
      Add( cache_vals, CoxeterNormalFormOfInversionSet( G, leaf[2] ) );
      p := Length( cache_keys );
    fi;
    Add( res, [ leaf[1], cache_vals[p] ] );
  od;
  return res;
end );

##
# Raggruppa le sottoespressioni di x per punto d'arrivo: restituisce
# [ keys, groups ], con keys = punti d'arrivo distinti (ordinati) e
# groups[j] = sottoespressioni che arrivano a keys[j].
InstallMethod( SubexpressionsOfCoxeterWordByEndpoint,
  "for a Coxeter group and a word",
  [ IsCoxeterGroup, IsList ],
function( G, x )
  local subs, endpoints, fibers, a;
  subs := SubexpressionsOfCoxeterWord( G, x );
  endpoints := Set( List( subs, a -> a[2] ) );
  fibers := List( endpoints, w -> [ ] );
  for a in subs do
    Add( fibers[ Position( endpoints, a[2] ) ], a[1] );
  od;
  return rec( endpoints := endpoints, fibers := fibers );
end );

##
# Si confrontano solo i gruppi di sottoespressioni di x e di y con lo
# stesso punto d'arrivo w, invece di tutte le coppie.
InstallMethod( DoubleLeavesIndicesOfHom,
  "for a Coxeter group and two words",
  [ IsCoxeterGroup, IsList, IsList ],
function( G, x, y )
  local gx, gy, res, j, p, w, e, f;
  gx := SubexpressionsOfCoxeterWordByEndpoint( G, x );
  gy := SubexpressionsOfCoxeterWordByEndpoint( G, y );
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

#############################################################
#############################################################
# Parte II -- la categoria CAP FreeBSCategory( G )
#
# Torre:  FreeBSCategory( G )  =  ReinterpretationOfCategory( Syn ),
#         Syn = SyntacticCategoryInDoctrines( "IsStrictMonoidalCategory" ).
#
# In Syn:
#   generatore s_i    : ObjectConstructor( Syn, Pair( "ObjectConstructor", [ Syn, nome_i ] ) )
#   parola x          : TensorProductOnListOfObjects( Syn, [ generatori ] )
#                       (anche per |x| <= 1: e' la forma che Syn stesso
#                        produce appiattendo i tensori)
#   light leaf        : MorphismConstructor( Syn, x, Pair( "MorphismConstructor",
#                                            [ Syn, "LL[ x, y, e, f, w ]" ] ), y )
#   strato [p,...]    : TensorProductOnListOfMorphisms( Syn, [ id_sinistra, LL, id_destra ] )
#   morfismo          : composizione (PreCompose) degli strati
#
# Ritorno da Syn: il termine sintattico viene letto ricorsivamente e trasformato in una lista di strati, poi messo in forma canonica.
#############################################################

# ---------- light leaves che sono identita' ----------
# leaf = [ x, y, e, f, w ]: e' l'identita' di x se x = y e se e, f scelgono l'intera espressione.
BindGlobal( "FreeBS_IsIdentityLeaf",
  leaf -> leaf[1] = leaf[2] and ForAll( leaf[3], i -> i = 1 )
                            and ForAll( leaf[4], i -> i = 1 ) );

# ---------- forma canonica (legge di scambio) ----------
#
# Strato l = [ p, x, y, e, f, w ]: agisce sulla parola u sostituendo
# u{[p+1..p+|x|]} = x con y. Due strati consecutivi l1, l2 (prima l1)
# si possono scambiare se l2 agisce interamente a sinistra
# (p2 + |x2| <= p1) o interamente a destra (p2 >= p1 + |y1|) dell'output
# di l1. Se valgono entrambe (|x2| = |y1| = 0, p1 = p2) si generano
# entrambi gli scambi: i due diagrammi sono isotopi.
# Prima di tutto si eliminano gli strati che sono identita' (vedi
# FreeBS_IsIdentityLeaf).
# La classe di equivalenza e' finita (stesso numero di strati, posizioni
# limitate); si restituisce il suo minimo lessicografico.
# Costo: proporzionale alla dimensione della classe (per k strati
# indipendenti fino a k!). Va bene per ora; in futuro si puo'
# sostituire con l'algoritmo quadratico di Delpeuch-Vicary.
InstallGlobalFunction( FreeBSCanonicalLayers,
function( layers )
  local swaps, seen, todo, seq, new;

  # la light leaf con x = y ed e = f = (1,...,1) e' l'identita' di x:
  # lo strato corrispondente si elimina
  layers := Filtered( layers, l -> not FreeBS_IsIdentityLeaf( l{[ 2 .. 6 ]} ) );

  swaps := function( seq )
    local res, i, l1, l2, p1, a1, b1, p2, a2, b2, s;
    res := [ ];
    for i in [ 1 .. Length( seq ) - 1 ] do
      l1 := seq[i];  l2 := seq[i+1];
      p1 := l1[1];  a1 := Length( l1[2] );  b1 := Length( l1[3] );
      p2 := l2[1];  a2 := Length( l2[2] );  b2 := Length( l2[3] );
      if p2 + a2 <= p1 then
        # l2 a sinistra: prima l2 (stessa posizione), poi l1 spostato
        s := ShallowCopy( seq );
        s[i]   := l2;
        s[i+1] := Concatenation( [ p1 - a2 + b2 ], l1{[ 2 .. 6 ]} );
        Add( res, s );
      fi;
      if p2 >= p1 + b1 then
        # l2 a destra: prima l2 spostato, poi l1 (stessa posizione)
        s := ShallowCopy( seq );
        s[i]   := Concatenation( [ p2 - b1 + a1 ], l2{[ 2 .. 6 ]} );
        s[i+1] := l1;
        Add( res, s );
      fi;
    od;
    return res;
  end;

  #ricerca sul grafo dei diagrammi isotopi (diagrammi collegati da un singolo scambio di strati, trovato da swaps). AddSet fa in modo che la lista seen sia ordinata lessicograficamente. In todo vengono salvati tutti i nodi del grafo.
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

# ---------- nomi delle light leaves in Syn ----------
BindGlobal( "FreeBS_LeafName",
  leaf -> Concatenation( "LL", String( leaf ) ) );

BindGlobal( "FreeBS_LeafOfName",
  name -> EvalString( name{[ 3 .. Length( name ) ]} ) );

# ---------- controlli ----------
BindGlobal( "FreeBS_CheckLeaf",
function( G, x, y, t )
  local e, f, w;
  FreeBS_CheckWord( G, x );
  FreeBS_CheckWord( G, y );
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
  FreeBS_CheckWord( G, w );
  if CoxeterNormalFormOfWord( G, w ) <> w then
    Error( "w must be given in normal form" );
  fi;
  if CoxeterNormalFormOfWord( G, x{ Positions( e, 1 ) } ) <> w or
     CoxeterNormalFormOfWord( G, y{ Positions( f, 1 ) } ) <> w then
    Error( "the subexpressions e and f do not both end in w" );
  fi;
end );

# ---------- la categoria ----------
InstallMethod( FreeBSCategory,
  "for a Coxeter group",
  [ IsCoxeterGroup ],
  #TODO: change with W istead of
function( G )
  local M, names, Syn, gen_obj, word_to_syn, syn_to_word, tensor_layers,
        syn_mor_to_layers, layers_to_syn, D;

  M := CoxeterMatrix( G );
  if ForAny( M, row -> infinity in row ) then
    Error( "Coxeter matrices with entries infinity are not supported (yet)" );
  fi;
  names := CoxeterGeneratorNames( G );

  Syn := SyntacticCategoryInDoctrines( "IsStrictMonoidalCategory" :
           with_given := true,
           name := Concatenation( "Syn( FreeBSCategory( ", String( M ), " ) )" ) );

  # parole <-> oggetti di Syn
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

  ## tensore di fattori [ parola sorgente, parola bersaglio, strati ]:
  ## il fattore k agisce dopo i fattori a sinistra, gia' arrivati al
  ## loro bersaglio
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

  ## morfismo di Syn -> lista di strati (non ancora canonica)
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

  ## (parola sorgente, strati) -> [ morfismo di Syn, parola bersaglio ]
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

  SetUnderlyingCoxeterGroup( D, G );

  ## uguaglianze: i dati sono canonici, quindi basta confrontarli
  ## (in Syn l'uguaglianza e' solo sintattica e IsCongruentForMorphisms
  ##  solleva un errore)
  ## (peso 1 < 50 = peso delle funzioni ereditate da Syn, altrimenti CAP
  ##  ignora queste)
  AddIsEqualForObjects( D, { D, a, b } -> BSWord( a ) = BSWord( b ), 1 );
  AddIsEqualForMorphisms( D, { D, a, b } -> BSLayers( a ) = BSLayers( b ), 1 );
  AddIsCongruentForMorphisms( D, { D, a, b } -> BSLayers( a ) = BSLayers( b ), 1 );

  Finalize( D );
  return D;
end );

# ---------- costruttori comodi ----------
InstallMethod( BSObject,
  "for a free BS category and a word",
  [ IsFreeBSCategory, IsList ],
function( D, x )
  FreeBS_CheckWord( UnderlyingCoxeterGroup( D ), x );
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
