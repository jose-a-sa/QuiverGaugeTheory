(* Wolfram Language Init File *)

(*** Fix for loading the package from parent folder ***)

$tempDir = Directory[];
SetDirectory[FileNameDrop[$InputFileName, -1]];
Get["QuiverGaugeTheory`"]
SetDirectory[$tempDir];
ClearAll[$tempDir];
Remove[$tempDir];

