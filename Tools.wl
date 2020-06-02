(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Tools`"]


UsageForm::usage = "";


ApplyTo::usage = "";


IndexedList::usage = "";


SubsetsOld::usage = "";


ExpandableBox::usage = "";


ExpandableBoxItem::usage = "";


Begin["`Private`"]


SyntaxInformation[UsageForm] = {"ArgumentsPattern" -> {_, _.}};

UsageForm[u: {__String}, a: ({__String} | HoldPattern[Alternatives][__String] | Automatic): Automatic] := 
    Map[UsageForm[#, a] &, u];
UsageForm[u_String, a: ({__String} | HoldPattern[Alternatives][__String] | Automatic): Automatic] :=
  Module[{uf, handleV, TIrule, funcPatt, varPatt, vars},
    Attributes[uf] = {HoldFirst};
    uf[patt_] := ToString[Unevaluated[patt], StandardForm];
    funcPatt = (WordBoundary ~~ Pattern[#1, WordCharacter ..] ~~ 
      Pattern[#2, ("[" ~~ Shortest[__] ~~ "]&" | "] &" | "]") ..]) &;
    vars = If[ a===Automatic,
      DeleteDuplicates@Flatten@StringCases[u, 
        funcPatt[func, args] :> StringCases[
          StringSplit[args, "[" | "]" | ","], 
            WordBoundary ~~ WordCharacter .. ~~ WordBoundary]
      ],
      a
    ];
    varPatt = (WordBoundary ~~ Pattern[#, __] ~~ WordBoundary /;
      StringMatchQ[#, Alternatives @@ vars]) &;
    TIrule = (varPatt[x] :> StringJoin["Style[", x, ",\"TI\"]"]);
    handleV = ReleaseHold@Map[uf, ToExpression[
      StringReplace[StringJoin[##], TIrule], 
      StandardForm, Hold], {1}] &;
    StringReplace[u, {
      q: funcPatt[func, args] :> handleV[q],
      varPatt[arg] :> handleV["Style[", arg, ",\"TI\"]"]
    }]
  ];


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


ExpandableBox[q_, header_, grid_, fmt_ : StandardForm] :=
  Module[{headerBox, frameBox, openBox, insideBox, dynamicBox},
    headerBox = Grid[{{
      Pane[Style[#1, FontSize -> 12, FontFamily -> "Helvetica"], 
        Alignment -> Left, 
        BaselinePosition -> Baseline, 
        FrameMargins -> {{4, 2}, {0, 0}}],
      Item[Pane[Setter[#2, {#3}, #4, 
            Appearance -> None, 
            ContentPadding -> False, 
            FrameMargins -> 0
          ], 
          Alignment -> Left, 
          FrameMargins -> {{2, 1}, {0, 0}}, 
          BaselinePosition -> {1, 1}
        ], 
        Frame -> {{Directive[ Opacity[0.5], RGBColor["#d4d8d9"] ], False}, 
          {False, False}}
      ]
      }}, 
      Alignment -> {{{Left}}, {{Baseline}}}, 
      ItemSize -> {{{Automatic}}, {{Automatic}}}, 
      Spacings -> {{{0}}, {{0}}}, 
      BaselinePosition -> {1, 1}
    ] &;
    openBox = Grid[
      {{#1}, {#2}}, 
      Alignment -> {{{Left}}, {{Baseline}}}, 
      Dividers -> {{{False}}, 
        {False, Directive[ Opacity[0.5], RGBColor["#d4d8d9"] ], False}}, 
      ItemSize -> {"Columns" -> {{Automatic}}, 
        "Rows" -> {{Automatic}}}, 
      BaselinePosition -> {1, 1}
    ] &;
    frameBox = Framed[#1,
      BaselinePosition -> Baseline, 
      FrameMargins -> {{0, 0}, {1, 1}}, 
      FrameStyle -> RGBColor["#d4d8d9"], 
      Background -> RGBColor["#f7f9fb"], 
      RoundingRadius -> 4, 
      DefaultBaseStyle -> {FontWeight -> Plain, 
        FontFamily -> CurrentValue["PanelFontFamily"]}
    ] &;
    insideBox = Pane[
      Grid[#, 
        Alignment -> {{{Left}}, {{Baseline}}}, 
        ItemSize -> {{{Automatic}}, {{Automatic}}},
        ItemStyle -> {{{Directive[FontSize -> 10]}}}, 
        Spacings -> {{0.5,{1.5},0.5}, {{0.4}}}
      ], 
      FrameMargins -> {{7, 7}, {4, 2}}, 
      Alignment -> Left, 
      BaselinePosition -> Baseline
    ] &;
    dynamicBox = DynamicModule[{open = False},
      Evaluate@PaneSelector[{
        False -> frameBox@headerBox[header, Dynamic[open], True, 
          Dynamic@RawBoxes@FrontEndResource["FEBitmaps", "IconizeOpener"]
        ],
        True -> frameBox@openBox[
          headerBox[header, Dynamic[open], False, 
            Dynamic@RawBoxes@FrontEndResource["FEBitmaps", "IconizeCloser"]
          ], 
          insideBox@grid
        ]}, 
        Dynamic[open], 
        ImageSize -> Automatic]
      ];
    With[{
      ib = Block[{BoxForm`UseTextFormattingQ = False},
        With[ {bx = dynamicBox}, MakeBoxes[bx, fmt] ] 
      ]},
      InterpretationBox[ib, q, Selectable -> False]
    ]
  ];


Options[ExpandableBoxItem] = {
  "ReplacementTest" -> MissingQ,
  "ReplacementValue" -> Nothing,
  BaseStyle -> {LineSpacing -> {1, 0}}
};

ExpandableBoxItem[{n_String, v_}, 
  opts: OptionsPattern[{ExpandableBoxItem, Row}] ] :=
  ExpandableBoxItem[{n, v}, Identity, opts];
ExpandableBoxItem[{n_String, v_}, g_: Identity,
  opts: OptionsPattern[{ExpandableBoxItem, Row}] ] := If[
    OptionValue["ReplacementTest"]@v, 
    OptionValue["ReplacementValue"],
    Row[{Style[ n, GrayLevel[0.5] ], g@v},
      Sequence @@ FilterRules[{opts}, 
        Except[Options@ExpandableBoxItem, Options@Row]
      ],
      BaseStyle -> OptionValue["BaseStyle"]
    ]
  ]


End[]


EndPackage[]