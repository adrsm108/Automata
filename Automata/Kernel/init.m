(* Mathematica Init file *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

Block[{Notation`AutoLoadNotationPalette = False},
  Get[FileNameJoin[{ParentDirectory@DirectoryName@$InputFileName, "Utils.m"}]];
  Needs["Notation`"];
  With[{
    style = StyleBox[#, FontWeight -> Bold, FontColor -> GrayLevel[0.5]] &,
    noEdit = Sequence @@ {Editable -> False, Selectable -> False},
    pbw = Notation`ParsedBoxWrapper, infix = Notation`InfixNotation,
    alias = Notation`AddInputAlias, note = Notation`Notation, wf = Notation`WorkingForm},

    With[{
      unionOp = pbw[TagBox[style["|"], Identity, noEdit, SyntaxForm -> "+"]],
      tradUnionOp = pbw[TagBox["|", Identity, SyntaxForm -> "+"]],
      concatOp = pbw[TagBox[style["\[RoundSpaceIndicator\]"], Identity, noEdit, SyntaxForm -> "*"]],
      tradConcatOp = pbw[TagBox["\[InvisibleSpace\]", Identity, SyntaxForm -> "*"]],
      esSym = pbw[TagBox[style["\[CurlyEpsilon\]"], Automata`EmptyString, noEdit]],
      tradEsSym = pbw[TagBox["\[CurlyEpsilon\]", Automata`EmptyString]],
      nullSym = pbw[TagBox[style["\[EmptySet\]"], Automata`RENull, noEdit]],
      tradNullSym = pbw[TagBox["\[EmptySet\]", Automata`RENull]]},

      infix[unionOp, Automata`REUnion];
      infix[tradUnionOp, Automata`REUnion, wf -> TraditionalForm];
      infix[concatOp, Automata`REConcat];
      infix[tradConcatOp, Automata`REConcat, wf -> TraditionalForm];
      note[DoubleLongLeftRightArrow[esSym, pbw["EmptyString"]]];
      note[DoubleLongLeftRightArrow[tradEsSym, pbw["EmptyString"]], wf -> TraditionalForm];
      note[DoubleLongLeftRightArrow[nullSym, pbw["RENull"]]];
      note[DoubleLongLeftRightArrow[tradNullSym, pbw["RENull"]], wf -> TraditionalForm];
      note[DoubleLongRightArrow[pbw[SuperscriptBox["a_", "*"]], pbw[RowBox[{"REClosure", "[", "a_", "]"}]]]];
      note[DoubleLongRightArrow[pbw[SuperscriptBox["a_", "*"]], pbw[RowBox[{"REClosure", "[", "a_", "]"}]]], wf -> TraditionalForm];
      note[DoubleLongLeftRightArrow[ pbw[OverscriptBox["a_", "\[LeftArrow]"]], pbw[RowBox[{"Automata`AutomatonReversal", "[", "a_", "]"}]]]];
      alias["re " -> concatOp];
      alias["re|" -> unionOp];
      alias["ree" -> esSym];
      alias["ren" -> nullSym];
      alias["ar" -> pbw[OverscriptBox["\[SelectionPlaceholder]", "\[LeftArrow]"]]];
    ]]]

