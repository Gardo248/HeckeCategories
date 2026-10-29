#############################################################
# FreeBSCategory.gd -- DICHIARAZIONI
#
# Parte I : livello combinatorio (elementi di W via insiemi di
#           inversioni, sottoespressioni, indici delle light leaves).
# Parte II: la categoria CAP FreeBSCategory( G ), costruita come
#           reinterpretazione della categoria sintattica Syn
#           (SyntacticCategoryInDoctrines, ToolsForCategoricalTowers).
#
# Si carica con FreeBSCategory.g (pacchetti + coxeter.g + questi file).
# TUTTA l'aritmetica e' esatta (interi e numeri ciclotomici).
#
# Convenzioni
#   - una parola x e' una lista di indici di generatori, es. [1,2,1];
#   - una sottoespressione e di x e' una lista 0/1 di pari lunghezza;
#   - il punto d'arrivo di e e' s_{x_1}^{e_1} ... s_{x_n}^{e_n};
#   - un elemento w di W e' rappresentato dalla sua forma normale.
#############################################################

#############################################################
# Parte I -- livello combinatorio
#############################################################

# Insieme di inversioni I(w) (lista ordinata di vettori nella base
# delle radici semplici). Determina w univocamente.
DeclareOperation( "InversionSetOfCoxeterWord",
                  [ IsCoxeterGroup, IsList ] );

# Insieme di inversioni di w*s_i, noto quello di w.
DeclareOperation( "InversionSetAfterRightMultiplication",
                  [ IsCoxeterGroup, IsList, IsPosInt ] );

# Forma normale dell'elemento con dato insieme di inversioni.
DeclareOperation( "CoxeterNormalFormOfInversionSet",
                  [ IsCoxeterGroup, IsList ] );

# Forma normale di una parola qualsiasi.
DeclareOperation( "CoxeterNormalFormOfWord",
                  [ IsCoxeterGroup, IsList ] );

# Tutte le sottoespressioni di x: lista di coppie [ e, w ].
DeclareOperation( "SubexpressionsOfCoxeterWord",
                  [ IsCoxeterGroup, IsList ] );

# Generatori di Hom(x,y): lista ordinata delle terne [ e, f, w ].
DeclareOperation( "LightLeafIndicesOfHom",
                  [ IsCoxeterGroup, IsList, IsList ] );

#############################################################
# Parte II -- la categoria CAP
#
# Oggetti:   parole x (dato: la lista x, attributo BSWord).
# Morfismi:  generati per composizione e prodotto tensoriale dalle
#            light leaves  LL(x,y,e,f,w) : x -> y.
#            Dato (attributo BSLayers): la lista degli "strati"
#                [ p, x, y, e, f, w ]
#            nell'ordine di composizione; lo strato agisce come
#            id_(p lettere a sinistra) (x) LL(x,y,e,f,w) (x) id_(resto).
#            La lista vuota e' l'identita'.
#            La light leaf LL(x,x,(1..1),(1..1),w), cioe' quella che
#            sceglie l'intera espressione in sorgente e bersaglio, E'
#            l'identita' di x: i suoi strati vengono eliminati.
#            Il dato e' sempre in FORMA CANONICA: il minimo
#            lessicografico nella classe generata dalla legge di
#            scambio (interchange law) tra strati adiacenti
#            indipendenti. Due morfismi sono uguali nella categoria
#            monoidale stretta libera se e solo se hanno lo stesso
#            dato canonico (Joyal-Street; Delpeuch-Vicary,
#            "Normalization for planar string diagrams", 2018).
# Nessuna relazione di Soergel e' imposta (categoria libera).
#############################################################

DeclareCategory( "IsFreeBSCategory", IsCapCategory );
DeclareCategory( "IsCellInFreeBSCategory", IsCapCategoryCell );
DeclareCategory( "IsObjectInFreeBSCategory",
                 IsCellInFreeBSCategory and IsCapCategoryObject );
DeclareCategory( "IsMorphismInFreeBSCategory",
                 IsCellInFreeBSCategory and IsCapCategoryMorphism );

DeclareAttribute( "UnderlyingCoxeterGroup", IsFreeBSCategory );
DeclareAttribute( "BSWord", IsObjectInFreeBSCategory );
DeclareAttribute( "BSLayers", IsMorphismInFreeBSCategory );

# Costruttore della categoria
DeclareAttribute( "FreeBSCategory", [ IsCoxeterGroup ] );

# L'oggetto corrispondente alla parola x
DeclareOperation( "BSObject", [ IsFreeBSCategory, IsList ] );

# Il generatore di Hom(x,y) di indice [ e, f, w ]
DeclareOperation( "LightLeafMorphism",
                  [ IsFreeBSCategory, IsList, IsList, IsList ] );

# Tutti i generatori di Hom(x,y), nell'ordine di LightLeafIndicesOfHom
DeclareOperation( "LightLeafMorphisms",
                  [ IsFreeBSCategory, IsList, IsList ] );

# Forma canonica di una lista di strati (vedi sopra)
DeclareGlobalFunction( "FreeBSCanonicalLayers" );
