(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`ExpandableBox`", {
  "QuiverGaugeTheory`Utils`"
}]


ExpandableBox::usage = "";


ExpandableBoxItem::usage = "";


Begin["`Private`"]


ExpandableBox[q_, header_, grid_, fmt_ : StandardForm] :=
  Module[{headerBox, frameBox, openBox, insideBox, dynamicBox},
    headerBox = Grid[{{
      Pane[Style[#1, FontSize -> 12, FontFamily -> "Helvetica"], 
        Alignment -> Left, 
        BaselinePosition -> Baseline, 
        FrameMargins -> {{4, 2}, {1, 0}}],
      Item[Pane[Setter[#2, {#3}, #4, 
            Appearance -> None, 
            ContentPadding -> False, 
            FrameMargins -> 0
          ], 
          Alignment -> Left, 
          FrameMargins -> {{2, 1}, {1, 0}}, 
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
        With[{bx = dynamicBox}, MakeBoxes[bx, fmt] ] 
      ]},
      InterpretationBox[ib, q, Selectable -> False]
    ]
  ];



Options[ExpandableBoxItem] = Normal@Association@{
  Splice@Options[Row],
  "ReplacementTest" -> MissingQ,
  "ReplacementValue" -> Nothing,
  BaseStyle -> {LineSpacing -> {1, 0}}
};

ExpandableBoxItem[{n_String, v_}, 
  opts: OptionsPattern[ExpandableBoxItem] ] :=
  ExpandableBoxItem[{n, v}, Identity, opts];
ExpandableBoxItem[{n_String, v_}, g_: Identity,
  opts: OptionsPattern[ExpandableBoxItem] ] := If[
    OptionValue["ReplacementTest"]@v, 
    OptionValue["ReplacementValue"],
    Row[{Style[ n, GrayLevel[0.5] ], g@v},
      Sequence @@ FilterRules[{opts}, 
        Options@ExpandableBoxItem
      ],
      BaseStyle -> OptionValue["BaseStyle"]
    ]
  ]


End[]


EndPackage[]