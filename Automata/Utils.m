(* Wolfram Language Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: Utils *)
(* :Context: Utils` *)
(* :Author: kvlox *)
(* :Date: 2020-05-19 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 12.1 *)
(* :Copyright: (c) 2020 kvlox *)
(* :Keywords: *)
(* :Discussion: *)

(* Declare package context *)
(*Package["Automata`"]*)

Package["Automata`"]

PackageScope["absOpt"]
PackageScope["rangeOver"]
PackageScope["aside"]
PackageScope["unless"]
PackageScope["when"]
PackageScope["filterOpts"]
PackageScope["validatedMethod"]
PackageScope["intProp"]
PackageScope["specificArguments"]
PackageScope["toAlternatives"]
PackageScope["autoAlt"]
PackageScope["rotateToFront"]
PackageScope["randomSubset"]
PackageScope["makeStateSummaryBoxes"]
PackageScope["makeAutomatonSummaryBoxes"]
PackageScope["mergeTransitions"]
PackageScope["sowPredicate"]
PackageScope["transitionLookup"]
PackageScope["updateState"]
PackageScope["updateStateRule"]
PackageScope["makeAlphabet"]
PackageScope["makeStateIDs"]

(* ::Section:: *)
(* Utils *)

(* ::Subsection:: *)
(* Clear Symbols *)
(*
Unprotect[$defaultDFAIcon, $defaultNFAIcon];
ClearAll[absOpt, rangeOver, aside, unless, when, filterOpts, validatedMethod, methodName, intProp, specificArguments,
  toAlternatives, autoAlt, randomSubset, rotateToFront, makeStateSummaryBoxes, makeAutomatonSummaryBoxes,
  mergeTransitions, sowPredicate, transitionLookup, updateState, updateStateRule, makeAlphabet,
  makeStateIDs, spanLength, makeStateIcon, makeStateUpperSummary, makeStateTransitionSummary, makeAutomatonUpperSummary,
  makeAutomatonStateSummary, $defaultDFAIcon, $defaultNFAIcon];
*)

(* ::Subsection:: *)
(* Macros *)

absOpt::usage = "absOpt[expr, name] returns the value of the rule obtained from AbsoluteOptions[expr, name]";
absOpt[expr_, name_] := AbsoluteOptions[expr, name][[1, 2]];

rangeOver::usage = "rangeOver[expr] returns Range[Length[expr]]
rangeOver[expr, i] returns Range[d_i], where d_i is the size of dimension i in expr.";
rangeOver[expr_] := Range[Length[expr]];
rangeOver[expr_, dim_] := Range[Extract[Dimensions[expr], dim]];

aside::usage = "aside[f, expr] evaluates f[expr], then returns expr.
aside[{f1, f2, ...}, expr] evaluates f1[expr], f2[expr], ... in sequence, then returns expr.
aside[funcs] represents an operator form of aside that can be applied to expressions.";
aside[f_, expr_] := (f[expr]; expr);
aside[f_][expr_] := (f[expr]; expr);
aside[fs_List, expr_] := (Do[f[expr], {f, fs}]; expr);
aside[fs_List][expr_] := (Do[f[expr], {f, fs}]; expr);

unless::usage = "unless[expr, form_1, alt_1, form_2, alt_2, ...] evaluates expr, then compares it to each of the form_i in turn, evaluating and returning the alt_i corresponding to the first match, or expr itself if no match is found.";
SetAttributes[unless, HoldRest];
unless[value_, alts : PatternSequence[_, _] ..] := Switch[value, alts, _, value];
SyntaxInformation[unless] = {"ArgumentsPattern" -> {_, _, __}};

when::usage = "when[expr, form] returns expr if it matches form, and Null otherwise.
when[expr, form, alt] returns expr if it matches form, and alt otherwise.";
SetAttributes[when, HoldRest];
when[expr_, form_] := If[MatchQ[expr, form], expr];
when[expr_, form_, alt_] := If[MatchQ[expr, form], expr, alt];

(* ::Subsection:: *)
(* Functions *)

filterOpts::usage = "filterOpts[{opt_1 -> v_1, opt_2 -> v_2, ...}, f] returns a sequence opt_i -> v_i where opt_i matches the left-hand side of a rule in Options[f].
filterOpts[{opt_1 -> v_1, ...}, {f1, f2, ...}] returns the sequence opt_i -> v_i, where opt_i matches the lhs of a rule in any of Options[f1], Options[f2], ...
filterOpts[opts, funcs, g] returns the sequence of opt_i -> v_i where opt_i matches some option of funcs, but does not match the lhs of any rule in Options[g]
filterOpts[opts, funcs, {g1, g2, ...}] returns the same, where opt_i does not match the lhs of any rule in Options[g1], Options[g2], ...
";
filterOpts[opts_?OptionQ, f_List] :=
    Sequence @@ FilterRules[opts, Catenate[Options /@ f]];
filterOpts[opts_?OptionQ, f_] := filterOpts[opts, {f}];
filterOpts[opts_?OptionQ, f_List, except_List] :=
    Sequence @@ Fold[FilterRules, opts,
      {Catenate[Options /@ f], Except[Catenate[Options /@ except]]}];
filterOpts[opts_?OptionQ, f_, except_] :=
    filterOpts[opts,
      If[ListQ@f, f, {f}],
      If[ListQ@except, except, {except}]];

validatedMethod::usage = "validatedMethod[given, {m1, m2, ...}, caller] returns given if it is one of {m1, m2, ...}. \
Otherwise, it issues the message caller::moptx, and returns Automatic.
validatedMethod[..., default] returns default instead of Automatic.";
validatedMethod[given_, expected_, caller_, default_ : Automatic] := With[
  {expectedNames = methodName /@ expected},
  If[MemberQ[expectedNames, methodName@given],
    methodName@given,
    Message[caller::moptx, given, caller, expectedNames]; default]];

methodName[{name_, ___}] := name;
methodName[name_] := name;

intProp::usage = "intProp[x, total] returns x if x is an integer, and Ceiling[x*total] otherwise.";
intProp[p_Integer, _] := p;
intProp[p_, tot_] := Ceiling[p * tot];

specificArguments::usage = "specificArguments[f] returns all the non-pattern expressions e for which f[e] has been explicitly defined.
specificArguments[f, True] also returns non-pattern expressions e1, e2, ... where f[e1|e2|...] has been explicitly defined.";
specificArguments[f_, separateAlternatives_ : False] :=
    If[separateAlternatives,
      specificArguments[f] /. {Alternatives -> Sequence},
      Cases[DownValues[f], HoldPattern[f[x_?(FreeQ[Pattern])]] :> x, {3}]];

toAlternatives::usage = "toAlternatives[{p1, p2, ...}] returns p1 | p2 | ...";
toAlternatives[{a_, b__}] := Alternatives[a, b];
toAlternatives[{a_}] := a;
toAlternatives[{}] := Alternatives[];

autoAlt::usage = "autoAlt[expr, alternative] returns alternative if expr === Automatic, and expr otherwise.";
SetAttributes[autoAlt, HoldRest];
autoAlt[value_, alt_] := If[value === Automatic, alt, value];

rotateToFront::notfound = "No subexpression matching `1` was found in `2`.";
rotateToFront::usage = "rotateToFront[expr, form] cycles the elements in expr to put the first element matching form in position 1";
rotateToFront[expr_, form_] := Catch@RotateLeft[expr,
  First@FirstPosition[expr, form, Message[rotateToFront::notfound, form, expr]; Throw[expr]] - 1];

randomSubset::usage = "randomSubset[{e_1, e_2, ...}] gives a pseudorandom subset of the e_i in pseudorandom order.
randomSubset[list, n] returns a list of n random subsets.
randomSubset[list, {imin, imax}] returns a pseudorandom subset of list with length between imin and imax.
randomSubset[list, {imin, imax}, n] returns n such random subsets.";
randomSubset::smplen = "randomSubset cannot generate subsets of maximum length `1`, which is greater than the length of the sample set `2`.";
randomSubset::invspec = "Invalid length specification `1` received at position 2 of randomSubset, where a pair of nondecreasing, nonnegative integers were expected.";
randomSubset[s_List] :=
    RandomSample[s, RandomVariate[BinomialDistribution[Length@s, 0.5]]];
randomSubset[s_List, n_Integer] := RandomSample[s, #] & /@ RandomVariate[BinomialDistribution[Length@s, 0.5], n];
randomSubset[s_List, {imin_Integer, imax_Integer}] :=
    RandomSample[s, RandomChoice[ Binomial[Length@s, Range[imin, imax]] -> Range[imin, imax]]] /;
        And[ 0 <= imin <= imax || Message[randomSubset::invspec, {imin, imax}],
          imax <= Length@s || Message[randomSubset::smplen, imax, s]];
randomSubset[s_List, {imin_Integer, imax_Integer}, n_Integer] :=
    RandomSample[s, #] & /@ RandomChoice[ Binomial[Length@s, Range[imin, imax]] -> Range[imin, imax], n] /;
        And[ 0 <= imin <= imax || Message[randomSubset::invspec, {imin, imax}],
          imax <= Length@s || Message[randomSubset::smplen, imax, s]];
randomSubset[s : (i_Integer ;; j_Integer ;; k_Integer : 1)] :=
    RandomSample[s, RandomVariate[BinomialDistribution[spanLength@s, 0.5]]];
randomSubset[s : (i_Integer ;; j_Integer ;; k_Integer : 1), n_Integer] :=
    RandomSample[s, #] & /@ RandomVariate[BinomialDistribution[spanLength@s, 0.5], n];
randomSubset[ s : (i_Integer ;; j_Integer ;; k_Integer : 1), {imin_Integer, imax_Integer}] :=
    RandomSample[s, RandomChoice[Binomial[spanLength@s, Range[imin, imax]] -> Range[imin, imax]]] /;
        And[ 0 <= imin <= imax || Message[randomSubset::invspec, {imin, imax}],
          imax <= spanLength@s || Message[randomSubset::smplen, imax, s]];
randomSubset[s : (i_Integer ;; j_Integer ;; k_Integer : 1), {imin_Integer, imax_Integer}, n_Integer] :=
    RandomSample[s, #] & /@ RandomChoice[ Binomial[spanLength@s, Range[imin, imax]] -> Range[imin, imax], n] /;
        And[ 0 <= imin <= imax || Message[randomSubset::invspec, {imin, imax}],
          imax <= spanLength@s || Message[randomSubset::smplen, imax, s]];

makeStateSummaryBoxes::usage = "makeStateSummaryBoxes[state] generates display boxes for the given DFA or NFA state.";
makeStateSummaryBoxes[s : (head : DFAState | NFAState)[___], form_] :=
    With[{color = Switch[head,
      DFAState, If[InitialQ@s, RGBColor[
        Rational[2, 3], 0.33333333333333337`, 0.33333333333333337`], RGBColor[
        0.275184, 0.392896, 0.719488]],
      NFAState,
      If[InitialQ@s, RGBColor[0.1454912, 0.533312, 0.6958304],
        RGBColor[0.9215, 0.5757, 0.07695]]]},
      BoxForm`ArrangeSummaryBox[
        None, s,
        makeStateIcon[s],
        makeStateUpperSummary[s],
        makeStateTransitionSummary[s],
        form, "Interpretable" -> True] /. {
        RowBox[{TagBox["None", "SummaryHead"], "[", \[FormalA]_,
          "]"}] -> \[FormalA]} /. {
        TemplateBox[\[FormalA]_, "SummaryPanel"] ->
            TemplateBox[\[FormalA],
              "StateSummaryPanel",
              DisplayFunction -> (FrameBox[#,
                Alignment -> {Left, Center},
                Appearance -> {"Default" -> None},
                FrameMargins -> {{7.5, 5}, {2.5, 5}},
                FrameStyle -> color,
                RoundingRadius -> 3,

                BaseStyle -> {Deployed -> False, Selectable -> False,
                  Background -> GrayLevel[1, 0.8]},
                DefaultBaseStyle -> {"Panel", Background -> None},
                BaselinePosition -> Baseline] &)]}];

makeAutomatonSummaryBoxes::usage = "makeAutomatonSummaryBoxes[A] generates display boxes for the given DFA or NFA.";
makeAutomatonSummaryBoxes[A : (head : NFA | DFA)[asc_],
  form : (StandardForm | TraditionalForm), maxiconstates_ : 15] :=
    Module[{icon, interp},
      icon = Lookup[asc, "icon",
        If[StateCount[A] <= maxiconstates,
          makeThumbnail[A],
          Switch[head, DFA, $defaultDFAIcon, NFA, $defaultNFAIcon]]];
      interp = If[KeyExistsQ[asc, "icon"], A,
        head[Append[asc, "icon" -> icon]]];
      BoxForm`ArrangeSummaryBox[
        head, interp, Deploy@icon,
        makeAutomatonUpperSummary[A],
        makeAutomatonStateSummary[A],
        form, "Interpretable" -> Automatic]];

mergeTransitions::usage = "mergeTransitions[{nfastate_1, nfastate_2, ...}] returns the association <|a_1 -> l_1 ... |>, where l_i = Union[nfastate_1[a_i], nfastate_2[a_i], ...].";
mergeTransitions[states : {NFAState[_, _?AssociationQ, _] ...}] := Merge[states[[All, 2]], Apply[Union]];

sowPredicate::usage = "sowPredicate[pred, tags] represents an operator that, when applied to x, yields pred[x], with the side effect Sow[x,tags] if pred[x] is True";
sowPredicate[pred_ -> f_, tags_ : None] :=
    With[{pval = pred[#]},
      If[pval, Sow[f@#, tags]; True, False, pval]] &;
sowPredicate[pred_, tags_ : None] :=
    With[{pval = pred[#]}, If[pval, Sow[#, tags]; True, False, pval]] &;

transitionLookup::usage = "transitionLookup[expr, {a1, a2, ...}] returns Transitions[expr, {a1, a2, ...}, Nothing] if expr is an explicit DFA or NFA state, and Lookup[expr, {a1, a2, ...}, Nothing] if expr is an association.";
transitionLookup[s_, All] := Values[s];
transitionLookup[s_?StateQ, symbols_List] := Transitions[s, symbols, Nothing];
transitionLookup[s_Association, symbols_List] := Lookup[s, symbols, Nothing];

updateState::usage = "updateState[state, f] returns a copy of state whose ID and transitions are renamed according to f
updateState[state, f, spec] returns a copy of state whose ID and transitions are renamed according to f, and whose initial/terminal specification is spec.
updateState[f] and updateState[f, spec] return operator forms of updateState that can be applied to states.";
updateState[DFAState[id_, d_, rest___], namefn_] := DFAState[namefn[id], namefn /@ d, rest];
updateState[s : DFAState[id_, d_, ___], namefn_, {init_, term_}] :=
    DFAState[namefn[id], namefn /@ d, {autoAlt[init, InitialQ@s], autoAlt[term, TerminalQ@s]}];
updateState[DFAState[id_, d_, ___], namefn_, rest_] := DFAState[namefn[id], namefn /@ d, rest];
updateState[NFAState[id_, d_, rest___], namefn_] := NFAState[namefn[id], Map[namefn, d, {2}], rest];
updateState[s : NFAState[id_, d_, ___], namefn_, {init_, term_}] :=
    NFAState[namefn[id], Map[namefn, d, {2}], {autoAlt[init, InitialQ@s], autoAlt[term, TerminalQ@s]}];
updateState[s : NFAState[id_, d_, ___], namefn_, rest_] := NFAState[namefn[id], Map[namefn, d, {2}], rest];
updateState[namefn_] := OperatorApplied[updateState][namefn];
updateState[namefn_, rest_] := OperatorApplied[updateState, {3, 1, 2}][namefn, rest];

updateStateRule::usage = "updateStateRule[state, f] returns a rule f[StateID[state]] -> updateState[state,f]
updateStateRule[state, f, spec] returns a rule f[StateID[state]] -> updateState[state, f, spec]
updateStateRule[f] and updateStateRule[f, spec] return an operator forms of updateStateRule that can be applied to states.";
updateStateRule[s : (DFAState | NFAState)[id_, ___], namefn_, rest___] := namefn[id] -> updateState[s, namefn, rest];
updateStateRule[namefn : Except[_NFAState | _DFAState]] := OperatorApplied[updateStateRule][namefn];
updateStateRule[namefn : Except[_NFAState | _DFAState], rest_] :=
    OperatorApplied[updateStateRule, {3, 1, 2}][namefn, rest];

makeAlphabet::usage = "makeAlphabet[k] returns an alphabet of length k, consisting of the first k letters in the English alphabet if k <= 26, or {\"x1\", \"x2\", ... , \"xk\"} otherwise.,
makeAlphabet[k, {a1, a2, ...}] returns {a1, ..., ak} if the given list has length >= k, or makeAlphabet[k] otherwise.
makeAlphabet[k, list, f] returns {f[1], f[2], ..., f[k]}. ";
makeAlphabet[k_, list_ : Automatic, f_ : Automatic] := Which[
  f =!= Automatic, Array[f, k],
  list =!= Automatic, Check[Take[list, k], makeAlphabet[k]],
  k <= 26, Take[Alphabet[], k],
  True, Array[StringTemplate["x``"], k]];

makeStateIDs::usage = "makeStateIDs[n] returns {1, 2, ..., n}
makeStateIDs[n, {q1, q2, ...}] returns {q1, q2, ..., qn} if the given list has length >= n, or makeStateIDs[n] otherwise.
makeStateIDs[n, list, f] returns {f[1], f[2], ..., f[n]}. ";
makeStateIDs[n_, list_ : Automatic, f_ : Automatic] := Which[
  f =!= Automatic, Array[f, n],
  list =!= Automatic, Check[Take[list, n], makeStateIDs[n]],
  True, Range[n]];

(* ::Subsubsection:: *)
(* Formatting *)

(* ::Subsection:: *)
(* Helper functions *)

spanLength[i_ ;; j_ ;; k_ : 1] := 1 + Floor[(j - i) / k];

makeStateIcon[(NFAState | DFAState)[id_, ___]] :=
    Deploy@Pane[Style[id, 12, ShowSyntaxStyles -> False],
      Alignment -> {Center, Center},
      ContentPadding -> False,
      FrameMargins -> {{1, 1}, {0, 0}},
      ImageSizeAction -> "ShrinkToFit",
      ImageSize ->
          Dynamic[{Automatic,
            3.5` CurrentValue["FontCapHeight"] /
                AbsoluteCurrentValue[Magnification]}]];

makeStateUpperSummary[state_] := {
  BoxForm`SummaryItem[{"Transitions: ", Length@Transitions@state}],
  BoxForm`SummaryItem[{"Accepting: ",
    If[TerminalQ@state, "Yes", "No"]}]};

makeStateTransitionSummary[(NFAState | DFAState)[_, <||>, ___], ___] = {};
makeStateTransitionSummary[NFAState[_, d_, ___], displaymax_ : 5] := {
  BoxForm`SummaryItem[{"Transitions: ", ""}],
  Grid[
    KeyValueMap[{#1, "\[Rule]",
      If[Length@#2 == 1, First@#2,
        Column[#2, {Left, Automatic}, {0, 0},
          BaselinePosition -> {1, Automatic}]]} &,
      Take[d, UpTo[displaymax]]
    ] ~ Append ~ If[Length@d > displaymax,
      {"", "\[VerticalEllipsis]", ""}, Nothing],
    Alignment -> {{Right, Center, Left}, Baseline},
    Spacings -> {{0, 0.3, 0.3, 0}, {0, {}, 0}}]};

makeStateTransitionSummary[DFAState[_, d_, ___], displaymax_ : 5] := {
  BoxForm`SummaryItem[{"Transitions: ", ""}],
  Splice[Normal[Take[d, UpTo[displaymax]]]],
  If[Length@d > displaymax,
    Item["\[VerticalEllipsis]", Alignment -> Center], Nothing]};

makeAutomatonUpperSummary[A_, displaymax_ : 3] :=
    With[{alph = Alphabet[A]},
      {BoxForm`SummaryItem[{"\[CapitalSigma]: ",
        If[MemberQ[alph, EmptyString],
          (alph /. {\[FormalA]___,
            EmptyString, \[FormalB]___} -> {\[FormalA], \[FormalB],
            EmptyString}) /.
              {h : Repeated[_, {displaymax}], _, __, t_, EmptyString}
                  :> Splice[{{h, "\[Ellipsis]", t, EmptyString},
                StringForm["  (``)", Length@alph]}],
          alph /. {h : Repeated[_, {displaymax}], _, __, t_}
              :> Splice[{{h, "\[Ellipsis]", t},
            StringForm["  (``)", Length@alph]}]]}],
        BoxForm`SummaryItem[{"States: ", StateCount[A]}]}];

makeAutomatonStateSummary[A_, displaymax_ : 3] := {
  Row[{
    BoxForm`SummaryItem[{"Initial: ", StateCount[A, "Initial"]}],
    BoxForm`SummaryItem[{"Terminal: ", StateCount[A, "Terminal"]}]},
    Spacer[3]],
  Splice@Take[States[A, "Initial", "Values"], UpTo[displaymax]],
  Splice@Lookup[States[A],
    Cases[IDs[A], Except[Alternatives @@ IDs[A, "Initial"]],
      {1}, Max[displaymax - StateCount[A, "Initial"], 0]]],
  If[StateCount[A] > displaymax,
    Item["\[VerticalEllipsis]", Alignment -> Center], Nothing]};

{$defaultDFAIcon, $defaultNFAIcon} = Uncompress[
  "1:eJxTTMoPSmNiYGAoZgESPpnFJWncIB4HkHAvSizIyEwuhsjzI4k45+\
cW5KRWpIIkuIAYRBs+tpF6ffmn/YoMLu+rzQwOry6d6yvc/89e7eoPkcuuX+2D5UX/rlH/\
aM/+0X3/meOf7efPceTc/fqn/TrNF5FZqs/tGaDAVz5jqtfbD/b7n+jfKfD5Chf/\
qpPnotn+wD4549P5HR9/2nfN9Ls59esT++ebH+as/PTIfsLzBrbJihftfzCfdpwRcMi+\
7dAJKU/m//YGmuvbQ66ssUfzJQsKjxHE44T4sNIntSw1p8gYDC7bQ+TYgYR/\
QWJyZkllEb+\
nR5Kw7RWoDCikXFPSU93yi3LBBvrl56VCpCDGA3mSKJahOMQTpNIQTBrhlDHGImMEkccpg\
1uPCRYZYzBpilPGDIuMOU57IDIWWGQscPrUAqcLTCFm4pSxxCJjidNtljjdZonTp2Y4XW2\
G0wVmnuBcYYAmBRHEah6SFLrzkKSwxZ4JTt+a4Aw7E6hveVHSJjOIByI8SlOL3gTukGt9/\
di+6PBXjZj+Q0DG2TMg8AZL0idfJyLTwB3pklmcnQlSWHRh+/\
SD7C9P26PJgXiofoKrLHqAoQXhM5C9Qe5Ozvk5+\
UUQCxjA4IE9nIFmE0hb0WnsrmDHI8eBR44VjxwnHjk2PHJceORYsMsFleakFoP0OSUmZ6c\
X5ZfmpWCGEjQG39pjMtBM4gSbVJwaXFKZg1IAAgOfASO5YLoCJJxYElJZkAqua0KKElMyS\
zLz8xJzsGgABaFbUWJuKlgopKg0FZuJIAUhmcnZxVjSGFgVD5DhmZuYnhqQmJKSmZcOrtF\
gGJYicNFY/A82KzizKhVRa7hU5iXmZiajpkawYsfSknygj2FyIC+\
FZAJ9BE2KPA5o4hAzQU52Li0qSs0rCUvMKU0N5gWHXV6Jc2KBR2pmekYJQltAfnlqEUSbC\
MjCpOL8nNKSVGTtxSDtvonpeZlpmcmJoPDO/A8EWPwWkJNfEpQIDCOUQMq+\
WXVUMuqSPWsip4yh43/\
7Bs6Hf0x4nexPu3kFvlnzCz2QBJENcs7JLCgAhjquOBRAVgyNIbSQ44IlLNIaK+\
9alLgcXO7bF3WvXv3x6V/7yyyx9qppL+xTUwqZml88sTdcsvTY1B2f7NnjZCoqT36w/\
5RtvkqM96V9VF/HvIMnv9kHsSmzJ2//Zr9Hz9yTt/w/vJGyx8craMHRL/ZJfctPGoT/\
s09wvPRua+Br+5Of8mc+uf8Trs4rZmOD6QYGh+upR3+\
KCP6079l4M6zo0BH7utXHzuTduzHsGiuGOKsuQ5zVPiEZ3E0SbG7D3SQh1IzB5gJznNU+\
bhkjnC7A3Swzwt6IQGjCFggWOD1kjNs4Qg1AbD7C3TQ0wW2RCU6LTHBaNJjbKtgbF0Vc1x\
cX2HK9ty8y5FgjE5UCNFX59s+6rD1b0CtncCtEUOiwf5zIWYJtFuKNZSfJ2Pi3GucC3Y/\
bF32fdCxDNvSpfRFT47klvldfY2t40cC1HLQxlpk2xrLQxlgu2hjLShtjOWljLBt2Y0fbq\
iO0fXllymS9pPJL9qZPl3TfmPvHXqPz+6w716/Zez3aq/Z961+\
qty8hvgGlwuDkxJzUlKJZM0FgpT0A9SPCtg=="];
Protect[$defaultDFAIcon, $defaultNFAIcon];

