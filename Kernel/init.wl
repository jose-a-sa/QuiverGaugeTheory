(* Wolfram Language Init File *)

Unprotect["QuiverGaugeTheory`Tools`*"];
ClearAll["QuiverGaugeTheory`Tools`*"];

Unprotect["QuiverGaugeTheory`Main`*"];
ClearAll["QuiverGaugeTheory`Main`*"];

Unprotect["QuiverGaugeTheory`Quiver`*"];
ClearAll["QuiverGaugeTheory`Quiver`*"];

Unprotect["QuiverGaugeTheory`Polytope`*"];
ClearAll["QuiverGaugeTheory`Polytope`*"];

Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];

Unprotect["QuiverGaugeTheory`Model`*"];
ClearAll["QuiverGaugeTheory`Model`*"];


Get["QuiverGaugeTheory`Tools`"]
Get["QuiverGaugeTheory`Main`"]
Get["QuiverGaugeTheory`Quiver`"]
Get["QuiverGaugeTheory`Polytope`"]
Get["QuiverGaugeTheory`Perturbations`"]
Get["QuiverGaugeTheory`Model`"]


With[{clearSyms = {}},
  Unprotect /@ clearSyms;
  ClearAll /@ clearSyms;
];

With[{syms = Names["QuiverGaugeTheory`Tools`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Main`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Quiver`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Polytope`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Perturbations`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

With[{syms = Names["QuiverGaugeTheory`Model`*"]},
  SetAttributes[syms, {ReadProtected}]
];
