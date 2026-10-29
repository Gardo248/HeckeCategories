#############################################################
# FreeBSCategoryTests.g -- test di FreeBSCategory
#   sezioni 0-5: livello combinatorio
#   sezione 6:   la categoria CAP FreeBSCategory( G )
# Uso (terminale WSL, dalla directory dei file):
#   gap -q FreeBSCategoryTests.g < /dev/null > tests_output.txt
#############################################################
Read( "FreeBSCategory.g" );
Print( "(le righe \"Error, ...\" stampate qui sotto sono errori ATTESI, catturati dai test)\n" );

TEST_COUNT := 0;  TEST_FAILED := 0;
Check := function( name, cond )
  TEST_COUNT := TEST_COUNT + 1;
  if not cond then TEST_FAILED := TEST_FAILED + 1; Print( "FAIL: ", name, "\n" ); fi;
end;
Bits := function( s ) return List( [ 1 .. Length( s ) ], i -> Int( [ s[i] ] ) ); end;
T := function( e, f, w ) return [ Bits( e ), Bits( f ), w ]; end;

# ---------- 0. nessun floating point nei file sorgente ----------
for f in [ "FreeBSCategory.gd", "FreeBSCategory.gi" ] do
  txt := StringFile( f );
  Check( Concatenation( f, ": niente Float" ),
         PositionSublist( txt, "Float" ) = fail and
         PositionSublist( txt, "FLOAT" ) = fail and
         PositionSublist( txt, "Cos(" ) = fail );
od;

# ---------- 1. S_3 ----------
G := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] );
s := 1; t := 2;
Check( "NF ss = e", CoxeterNormalFormOfWord( G, [s,s] ) = [] );
Check( "NF sts = tst", CoxeterNormalFormOfWord( G, [s,t,s] ) = CoxeterNormalFormOfWord( G, [t,s,t] ) );
Check( "NF sts = [1,2,1]", CoxeterNormalFormOfWord( G, [t,s,t] ) = [1,2,1] );
Check( "|I(sts)| = 3", Length( InversionSetOfCoxeterWord( G, [s,t,s] ) ) = 3 );
Check( "Hom(e,e)", LightLeafIndicesOfHom( G, [], [] ) = [ [ [], [], [] ] ] );
Check( "Hom(s,s)", Set( LightLeafIndicesOfHom( G, [s], [s] ) ) = Set( [ T("0","0",[]), T("1","1",[1]) ] ) );
Check( "Hom(t,t)", Set( LightLeafIndicesOfHom( G, [t], [t] ) ) = Set( [ T("0","0",[]), T("1","1",[2]) ] ) );
Check( "Hom(ss,s)", Set( LightLeafIndicesOfHom( G, [s,s], [s] ) ) =
      Set( [ T("00","0",[]), T("11","0",[]), T("10","1",[1]), T("01","1",[1]) ] ) );
user := [ ["000","000",[]],["101","000",[]],["000","110",[]],["101","110",[]],
          ["000","101",[]],["101","101",[]],["000","011",[]],["101","011",[]],
          ["100","100",[1]],["100","010",[1]],["100","001",[1]],["100","111",[1]],
          ["001","100",[1]],["001","010",[1]],["001","001",[1]],["001","111",[1]] ];
user := List( user, a -> T( a[1], a[2], a[3] ) );
got := LightLeafIndicesOfHom( G, [s,t,s], [s,s,s] );
Check( "Hom(sts,sss): 16 generatori come da elenco", Length( got ) = 16 and Set( got ) = Set( user ) );

# ---------- 2. confronto con l'oracolo ESATTO del gruppo fp (gruppi finiti) ----------
# (uguaglianza in un gruppo fp finito = enumerazione dei laterali, aritmetica esatta)
CheckAgainstFp := function( M, name, N, L )
  local G, gens, n, k, w1, w2, nf1, same, el;
  G := CoxeterGroupByMatrix( M );  gens := GeneratorsOfGroup( G );  n := Length( M );
  el := w -> Product( gens{ w }, One( G ) );
  for k in [ 1 .. N ] do
    w1 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    w2 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    same := ( el( w1 ) = el( w2 ) );
    Check( Concatenation( name, ": NF uguale <=> elementi uguali" ),
           same = ( CoxeterNormalFormOfWord( G, w1 ) = CoxeterNormalFormOfWord( G, w2 ) ) );
    nf1 := CoxeterNormalFormOfWord( G, w1 );
    Check( Concatenation( name, ": NF e' una parola dello stesso elemento" ), el( nf1 ) = el( w1 ) );
    Check( Concatenation( name, ": NF non piu' lunga, stessa parita'" ),
           Length( nf1 ) <= Length( w1 ) and ( Length( w1 ) - Length( nf1 ) ) mod 2 = 0 );
    Check( Concatenation( name, ": |I(w)| = lunghezza NF" ),
           Length( InversionSetOfCoxeterWord( G, w1 ) ) = Length( nf1 ) );
    Check( Concatenation( name, ": NF idempotente" ), CoxeterNormalFormOfWord( G, nf1 ) = nf1 );
    Check( Concatenation( name, ": w * w^-1 = e" ),
           CoxeterNormalFormOfWord( G, Concatenation( w1, Reversed( w1 ) ) ) = [] );
  od;
end;
CheckAgainstFp( [[1,3,2],[3,1,3],[2,3,1]], "A3", 150, 9 );
CheckAgainstFp( [[1,3,2],[3,1,4],[2,4,1]], "B3", 150, 9 );
CheckAgainstFp( [[1,3,2],[3,1,5],[2,5,1]], "H3", 80, 9 );   # usa sqrt(5)
CheckAgainstFp( [[1,5],[5,1]], "I2(5)", 60, 10 );
CheckAgainstFp( [[1,7],[7,1]], "I2(7)", 60, 12 );           # usa cos(pi/7)

# ---------- 3. gruppi infiniti: confronto con l'uguaglianza ESATTA delle matrici di Tits ----------
CheckAgainstTits := function( M, name, N, L, infinite_irreducible )
  local mats, n, k, w1, w2, G, mat, same;
  G := CoxeterGroupByMatrix( M );  mats := CoxeterReflectionMatrices( G );  n := Length( M );
  mat := w -> Product( mats{ w }, IdentityMat( n ) );
  for k in [ 1 .. N ] do
    w1 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    w2 := List( [ 1 .. Random( [ 0 .. L ] ) ], i -> Random( [ 1 .. n ] ) );
    same := ( mat( w1 ) = mat( w2 ) );
    Check( Concatenation( name, ": NF uguale <=> matrici di Tits uguali" ),
           same = ( CoxeterNormalFormOfWord( G, w1 ) = CoxeterNormalFormOfWord( G, w2 ) ) );
    Check( Concatenation( name, ": NF = stessa matrice" ),
           mat( CoxeterNormalFormOfWord( G, w1 ) ) = mat( w1 ) );
    Check( Concatenation( name, ": w * w^-1 = e" ),
           CoxeterNormalFormOfWord( G, Concatenation( w1, Reversed( w1 ) ) ) = [] );
  od;
  # in un gruppo di Coxeter infinito irriducibile le potenze di un elemento
  # di Coxeter sono ridotte (Speyer)
  if infinite_irreducible then
    w1 := Concatenation( List( [ 1 .. 6 ], i -> [ 1 .. n ] ) );
    Check( Concatenation( name, ": (s1...sn)^6 e' ridotta" ),
           Length( CoxeterNormalFormOfWord( G, w1 ) ) = 6 * n );
  fi;
end;
CheckAgainstTits( [[1,3,3],[3,1,3],[3,3,1]], "affine A2~", 150, 14, true );
CheckAgainstTits( [[1,4,2],[4,1,4],[2,4,1]], "affine B2~", 150, 14, true );
CheckAgainstTits( [[1,3,7],[3,1,3],[7,3,1]], "iperbolico (7,3,3)", 100, 14, true );
CheckAgainstTits( [[1,3,2,2],[3,1,3,3],[2,3,1,2],[2,3,2,1]], "D4 (finito, via Tits)", 100, 12, false );

# ---------- 4. gruppo infinito: conteggio a mano ----------
G := CoxeterGroupByMatrix( [[1,4,2],[4,1,4],[2,4,1]] );
Check( "affine B2~, Hom(121,121) ha 12 generatori", Length( LightLeafIndicesOfHom( G, [1,2,1], [1,2,1] ) ) = 12 );
Check( "affine B2~, braid m=4", CoxeterNormalFormOfWord( G, [1,2,1,2] ) = CoxeterNormalFormOfWord( G, [2,1,2,1] ) );
Check( "affine B2~, commutazione", CoxeterNormalFormOfWord( G, [1,3] ) = CoxeterNormalFormOfWord( G, [3,1] ) );
Check( "affine B2~, 121 <> 212", CoxeterNormalFormOfWord( G, [1,2,1] ) <> CoxeterNormalFormOfWord( G, [2,1,2] ) );

# ---------- 5. errori ----------
G := CoxeterGroupByMatrix( [[1,3],[3,1]] );
old := BreakOnError;  BreakOnError := false;
res := CALL_WITH_CATCH( CoxeterNormalFormOfWord, [ G, [3] ] );
BreakOnError := old;
Check( "lettera fuori range -> errore", res[1] = false );


# ---------- 6. la categoria CAP FreeBSCategory ----------
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

G := CoxeterGroupByMatrix( [[1,3],[3,1]], ["s","t"] );
D := FreeBSCategory( G );
Ob := w -> BSObject( D, w );
Check( "IsFreeBSCategory", IsFreeBSCategory( D ) );
Check( "IsStrictMonoidalCategory", IsStrictMonoidalCategory( D ) );

# oggetti
Check( "tensore di oggetti", BSWord( TensorProductOnObjects( Ob( [1] ), Ob( [2,1] ) ) ) = [ 1, 2, 1 ] );
Check( "unita' = parola vuota", BSWord( TensorUnit( D ) ) = [ ] );
Check( "unita' neutra", IsEqualForObjects( TensorProductOnObjects( TensorUnit( D ), Ob( [1,2] ) ), Ob( [1,2] ) ) );

# generatori di Hom
hom := LightLeafMorphisms( D, [1,2,1], [1,1,1] );
Check( "Hom(sts,sss): 16 generatori", Length( hom ) = 16 );
Check( "generatori distinti",
       ForAll( Combinations( [ 1 .. 16 ], 2 ), p -> not EqM( hom[p[1]], hom[p[2]] ) ) );
Check( "sorgente e bersaglio dei generatori",
       ForAll( hom, h -> BSWord( Source( h ) ) = [1,2,1] and BSWord( Range( h ) ) = [1,1,1] ) );
Check( "numero di generatori = LightLeafIndicesOfHom",
       ForAll( [ [ [], [] ], [ [1], [1] ], [ [1,1], [1] ], [ [1,2,1], [2,1,2] ] ],
               p -> Length( LightLeafMorphisms( D, p[1], p[2] ) ) =
                    Length( LightLeafIndicesOfHom( G, p[1], p[2] ) ) ) );

dot  := LightLeafMorphism( D, [1], [], [ [0], [], [] ] );   # s -> vuoto
udot := LightLeafMorphism( D, [], [1], [ [], [0], [] ] );   # vuoto -> s
Check( "dato di un generatore", BSLayers( dot ) = [ [ 0, [1], [], [0], [], [] ] ] );
Check( "LL(s,s,1,1,s) = id_s", EqM( LightLeafMorphism( D, [1], [1], [ [1], [1], [1] ] ), IdM( Ob( [1] ) ) ) );
Check( "LL(e,e,-,-,e) = id dell'unita'",
       EqM( LightLeafMorphism( D, [], [], [ [], [], [] ] ), IdM( TensorUnit( D ) ) ) );
Check( "LL(ss,ss,11,11,e) = id_ss (parola non ridotta)",
       EqM( LightLeafMorphism( D, [1,1], [1,1], [ [1,1], [1,1], [] ] ), IdM( Ob( [1,1] ) ) ) );
Check( "LL(sts,sts,111,111,sts) = id_sts",
       EqM( LightLeafMorphism( D, [1,2,1], [1,2,1], [ [1,1,1], [1,1,1], [1,2,1] ] ), IdM( Ob( [1,2,1] ) ) ) );
Check( "Hom(sts,sts): esattamente un generatore e' l'identita'",
       Number( LightLeafMorphisms( D, [1,2,1], [1,2,1] ), m -> EqM( m, IdM( Ob( [1,2,1] ) ) ) ) = 1 );
Check( "LL(s,s,0,0,e) non e' l'identita'",
       not EqM( LightLeafMorphism( D, [1], [1], [ [0], [0], [] ] ), IdM( Ob( [1] ) ) ) );

# assiomi di categoria
f := LightLeafMorphisms( D, [1,2], [2,1] )[2];
g := LightLeafMorphisms( D, [2,1], [1] )[1];
h := LightLeafMorphisms( D, [1], [1,1] )[1];
Check( "associativita' della composizione",
       EqM( PreCompose( PreCompose( f, g ), h ), PreCompose( f, PreCompose( g, h ) ) ) );
Check( "identita' a sinistra", EqM( PreCompose( IdM( Source( f ) ), f ), f ) );
Check( "identita' a destra",   EqM( PreCompose( f, IdM( Range( f ) ) ), f ) );
Check( "sorgente/bersaglio della composizione",
       BSWord( Source( PreCompose( f, g ) ) ) = [1,2] and BSWord( Range( PreCompose( f, g ) ) ) = [1] );

# assiomi monoidali
Check( "associativita' del tensore", EqM( Tns( Tns( f, g ), h ), Tns( f, Tns( g, h ) ) ) );
Check( "id_x (x) id_y = id_xy", EqM( Tns( IdM( Ob( [1] ) ), IdM( Ob( [2,1] ) ) ), IdM( Ob( [1,2,1] ) ) ) );
Check( "id_unita' (x) f = f", EqM( Tns( IdM( TensorUnit( D ) ), f ), f ) );
Check( "f (x) id_unita' = f", EqM( Tns( f, IdM( TensorUnit( D ) ) ), f ) );
Check( "legge di scambio (1)",
       EqM( PreCompose( Tns( f, IdM( Source( g ) ) ), Tns( IdM( Range( f ) ), g ) ), Tns( f, g ) ) );
Check( "legge di scambio (2)",
       EqM( PreCompose( Tns( IdM( Source( f ) ), g ), Tns( f, IdM( Range( g ) ) ) ), Tns( f, g ) ) );
a1 := LightLeafMorphisms( D, [1], [1,1] )[2];  b1 := LightLeafMorphisms( D, [1,1], [] )[1];
a2 := LightLeafMorphisms( D, [2], [] )[1];     b2 := LightLeafMorphisms( D, [], [2,2] )[1];
Check( "funtorialita' del tensore",
       EqM( Tns( PreCompose( a1, b1 ), PreCompose( a2, b2 ) ),
            PreCompose( Tns( a1, a2 ), Tns( b1, b2 ) ) ) );
Check( "il tensore non e' commutativo", BSLayers( Tns( f, h ) ) <> BSLayers( Tns( h, f ) ) );

# casi con parti vuote (morfismi da/verso l'unita')
Check( "dot (x) udot = udot o dot", EqM( Tns( dot, udot ), PreCompose( dot, udot ) ) );
Check( "udot (x) dot = udot o dot", EqM( Tns( udot, dot ), PreCompose( dot, udot ) ) );
Check( "udot o dot <> id_s", not EqM( PreCompose( dot, udot ), IdM( Ob( [1] ) ) ) );
sc := PreCompose( udot, dot );                              # endomorfismo dell'unita'
Check( "scalare <> id dell'unita'", not EqM( sc, IdM( TensorUnit( D ) ) ) );
Check( "scalare a sinistra <> a destra di una linea (niente braiding)",
       not EqM( Tns( sc, IdM( Ob( [1] ) ) ), Tns( IdM( Ob( [1] ) ), sc ) ) );
Check( "scalari: sc (x) sc = sc o sc", EqM( Tns( sc, sc ), PreCompose( sc, sc ) ) );

# in Syn (uguaglianza puramente sintattica) la composizione NON e'
# associativa: i due alberi sono diversi. Questo test documenta il fatto.
Syn := ModelingCategory( D );
mf := ModelingMorphism( D, f );  mg := ModelingMorphism( D, g );  mh := ModelingMorphism( D, h );
Check( "in Syn (f g) h e f (g h) sono termini diversi",
       not IsEqualForMorphisms( Syn, PreCompose( Syn, PreCompose( Syn, mf, mg ), mh ),
                                     PreCompose( Syn, mf, PreCompose( Syn, mg, mh ) ) ) );

# forma canonica direttamente
Check( "FreeBSCanonicalLayers idempotente",
       FreeBSCanonicalLayers( BSLayers( Tns( f, g ) ) ) = BSLayers( Tns( f, g ) ) );

# un gruppo infinito
G3 := CoxeterGroupByMatrix( [[1,3,3],[3,1,3],[3,3,1]] );
D3 := FreeBSCategory( G3 );
Check( "affine A2~: Hom(123,123)",
       Length( LightLeafMorphisms( D3, [1,2,3], [1,2,3] ) ) =
       Length( LightLeafIndicesOfHom( G3, [1,2,3], [1,2,3] ) ) );

# errori
CheckErr( "terna non valida -> errore", { } -> LightLeafMorphism( D, [1], [1], [ [1], [0], [1] ] ) );
CheckErr( "lettera fuori range -> errore", { } -> BSObject( D, [ 3 ] ) );
CheckErr( "m = infinity -> errore",
          { } -> FreeBSCategory( CoxeterGroupByMatrix( [[1,infinity],[infinity,1]] ) ) );

Print( "\n", TEST_COUNT - TEST_FAILED, " / ", TEST_COUNT, " test superati" );
if TEST_FAILED = 0 then Print( " -- TUTTO OK\n" ); else Print( " -- ", TEST_FAILED, " FALLITI\n" ); fi;
QUIT;
