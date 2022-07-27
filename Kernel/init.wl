(* Wolfram Language Init File *)

With[{clearSyms = {CenterDot, NonCommutativeMultiply}},
  Unprotect /@ clearSyms;
  ClearAll /@ clearSyms;
];


Get["QuiverGaugeTheory`Utils`"]
Get["QuiverGaugeTheory`ExpandableBox`"]

Get["QuiverGaugeTheory`Core`"]
Get["QuiverGaugeTheory`Quiver`"]
Get["QuiverGaugeTheory`Tiling`"]
Get["QuiverGaugeTheory`Polytope`"]
Get["QuiverGaugeTheory`Moduli`"]
Get["QuiverGaugeTheory`Perturbations`"]
Get["QuiverGaugeTheory`Model`"]


SetAttributes[CenterDot, {Protected, ReadProtected}];
SetAttributes[NonCommutativeMultiply, {Protected, ReadProtected}];


SetOptions[Simplify, 
  TransformationFunctions -> {Automatic,
    Replace[c_CenterDot?OrderedMesonQ :> RotateLeft[c, 
      First@Ordering[c] - 1] 
    ]}
];
SetOptions[FullSimplify, 
  TransformationFunctions -> {Automatic,
    Replace[c_CenterDot?OrderedMesonQ :> RotateLeft[c, 
      First@Ordering[c] - 1] 
    ]}
];

