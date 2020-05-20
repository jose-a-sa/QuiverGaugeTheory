(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Tools`"]


Unprotect["QuiverGaugeTheory`Tools`*"];
ClearAll["QuiverGaugeTheory`Tools`*"];


ApplyTo::usage = "";


IndexedList::usage = "";


SubsetsOld::usage = "";


Begin["`Private`"]


SyntaxInformation[ApplyTo] = {"ArgumentsPattern" -> {_, _.}};

ApplyTo[f_, levelspec_ : {0}] := 
  Apply[f, #, levelspec] &;


SyntaxInformation[IndexedList] = {"ArgumentsPattern" -> {_, _., _.}};

IndexedList[l_List] := Transpose[{Range@Length@l, l}]
IndexedList[l_List, n0_] := 
  Transpose[{Range[n0, Length[l] + (n0 - 1)], l}]
IndexedList[l_List, n0_, di_] := 
  Transpose[{Range[n0, n0 + di (Length[l] - 1), di], l}]


(* FLAG: added compatibility with < 12.0 *)
SyntaxInformation[SubsetsOld] = {"ArgumentsPattern" -> {_, _.}};

SubsetsOld[l_List] :=
  SubsetsOld[l, All];
SubsetsOld[l_List, All] :=
  SubsetsOld[l, {0, Infinity}];
SubsetsOld[l_List, n_Integer] :=
  SubsetsOld[l, {0, n}];
SubsetsOld[l_List, {n_Integer}] :=
  SubsetsOld[l, {n, n}];
SubsetsOld[l_List, {n_Integer,m:(_Integer|Infinity)}] := 
  SubsetsOld[l, {n, m, 1}];
SubsetsOld[l_List, {n_Integer, m:(_Integer|Infinity), s_Integer}] := 
  {} /; Or[step (nmax - nmin) < 0, step==0];
SubsetsOld[l_List, {n_Integer, m:(_Integer|Infinity), s_Integer}] := 
  Cases[
    Join @@ Table[Tuples[Range@Length@l, i], {i, n, Min[n, Length@l], s}], 
    {a___Integer} :> l[[{a}]] /; Less[a] 
  ];


With[{syms = Names["QuiverGaugeTheory`Tools`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[]


EndPackage[]