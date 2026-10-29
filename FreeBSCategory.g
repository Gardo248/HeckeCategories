#############################################################
# FreeBSCategory.g -- file di caricamento
#
# Uso (da GAP, con la directory di lavoro = quella dei file):
#   Read( "FreeBSCategory.g" );
# Non si puo' rileggere nella stessa sessione (Declare*): riavvia GAP.
#############################################################
for pkg in [ "MonoidalCategories", "ToolsForCategoricalTowers" ] do
  if LoadPackage( pkg, false ) <> true then
    Error( "the package ", pkg, " is needed" );
  fi;
od;
Unbind( pkg );
Read( "coxeter.g" );
Read( "FreeBSCategory.gd" );
Read( "FreeBSCategory.gi" );
