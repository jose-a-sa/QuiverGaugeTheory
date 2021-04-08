BeginPackage["QuiverGaugeTheory`Tiling`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`"
}]


PerfectMatchingMatrix::usage = "";


Begin["`Private`"]


PerfectMatchingMatrix[W_?ToricPotentialQ] :=
  Module[{sp, terms, k, fs, pmList, x = \[FormalX]},
    sp = ExpandAll@If[AbelianPotentialQ@W,
      NonAbelianizeMesons[W], W];
    If[sp === $Failed, Return[$Failed] ];
    fs = First /@ PositionIndex@Fields[sp];
    terms = GroupBy[
      Cases[sp, HoldPattern[Times][x_., c_?FieldProductQ] :> {x, c}],
      First -> Last
    ];
    k = ReplaceAll[fs]@Array[
      Sum[x[e] Boole@AllTrue[{terms[1][[#1]], terms[-1][[#2]]}, MemberQ@e], 
        {e, Keys@fs}] &,
      {Length@terms[1], Length@terms[-1]}
    ];
    pmList = List @@@ List @@ Expand@Permanent[k] // 
      ReplaceAll[x -> Identity]; 
    Boole@Outer[MatchQ[#1, #2] &, 
      Range@Length[fs], (Alternatives @@@ pmList), 1]
  ]


End[]

EndPackage[]