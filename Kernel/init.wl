(* Wolfram Language Init File *)

With[{clearSyms = {CenterDot, NonCommutativeMultiply}},
  Unprotect /@ clearSyms;
  ClearAll /@ clearSyms;
];

Unprotect["QuiverGaugeTheory`Tools`*"];
ClearAll["QuiverGaugeTheory`Tools`*"];

Unprotect["QuiverGaugeTheory`ExpandableBox`*"];
ClearAll["QuiverGaugeTheory`ExpandableBox`*"];

Unprotect["QuiverGaugeTheory`Core`*"];
ClearAll["QuiverGaugeTheory`Core`*"];

Unprotect["QuiverGaugeTheory`Quiver`*"];
ClearAll["QuiverGaugeTheory`Quiver`*"];

Unprotect["QuiverGaugeTheory`Tiling`*"];
ClearAll["QuiverGaugeTheory`Tiling`*"];

Unprotect["QuiverGaugeTheory`Polytope`*"];
ClearAll["QuiverGaugeTheory`Polytope`*"];

Unprotect["QuiverGaugeTheory`Moduli`*"];
ClearAll["QuiverGaugeTheory`Moduli`*"];

Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];

Unprotect["QuiverGaugeTheory`Model`*"];
ClearAll["QuiverGaugeTheory`Model`*"];

(* With[
  {syms = Map["QuiverGaugeTheory`Model`" <> # &, 
    DeleteCases[
      Names["QuiverGaugeTheory`Model`*"],
      "ModelData"
    ]
  ]},
  Unprotect /@ syms;
  ClearAll /@ syms;
] *)


Get["QuiverGaugeTheory`Tools`"]
Get["QuiverGaugeTheory`ExpandableBox`"]

Get["QuiverGaugeTheory`Core`"]
Get["QuiverGaugeTheory`Quiver`"]
Get["QuiverGaugeTheory`Tiling`"]
Get["QuiverGaugeTheory`Polytope`"]
Get["QuiverGaugeTheory`Moduli`"]
Get["QuiverGaugeTheory`Perturbations`"]
Get["QuiverGaugeTheory`Model`"]


SetOptions[Simplify, TransformationFunctions -> {Automatic, 
  Replace[c_CenterDot?OrderedMesonQ :> RotateLeft@c]
}];
SetOptions[FullSimplify, TransformationFunctions -> {Automatic, 
  Replace[c_CenterDot?OrderedMesonQ :> RotateLeft@c]
}];


With[{syms = Names["QuiverGaugeTheory`Tools`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`ExpandableBox`*"]},
  SetAttributes[syms, {ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Core`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];
SetAttributes[CenterDot, {Protected, ReadProtected}];
SetAttributes[NonCommutativeMultiply, {Protected, ReadProtected}];

With[{syms = Names["QuiverGaugeTheory`Quiver`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Tiling`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Polytope`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Moduli`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Perturbations`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Model`*"]},
  SetAttributes[syms, {Protected, ReadProtected}];
];
