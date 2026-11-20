#############################################################
# FreeBSCategory.g -- loading file
#
# Usage (from GAP, with the working directory = that of the files):
#   Read( "FreeBSCategory.g" );
# It cannot be re-read in the same session (Declare*): restart GAP.
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
