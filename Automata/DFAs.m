(* Wolfram Language Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: DFAs *)
(* :Context: DFAs` *)
(* :Author: kvlox *)
(* :Date: 2020-05-15 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 12.1 *)
(* :Copyright: (c) 2020 kvlox *)
(* :Keywords: *)
(* :Discussion: *)

Package["Automata`"]

PackageExport["DFAState"]
PackageExport["DFAQ"]
PackageExport["DFA"]
PackageExport["RandomDFA"]
PackageExport["FactorDFA"]
PackageExport["ToDFA"]
PackageExport["MinimizeDFA"]

PackageScope["dfaAscQ"]
PackageScope["productDFA"]
PackageScope["scanProductDFA"]

(* ::Section:: *)
(* DFAs *)

(* ::Subsection:: *)
(* Clear Symbols *)
(*
ClearAll[ DFAState, DFAQ, DFA, RandomDFA, FactorDFA, ToDFA, MinimizeDFA, dfaAscQ, productDFA, scanProductDFA,
  validDFAInputQ, validDFAInitQ, productStates
];
*)


(* ::Subsection:: *)
(* Exported Functions *)

DFAState::usage = "DFAState[q, <|a_1 -> q_1, ...|>] represents the nonterminal state with ID q in a DFA with transitions \[Delta](q, a_i) = q_i.
DFAState[q, Transitions, term] represents a state which is terminal if term is True.
DFAState[q, Transitions, {init, term}] represents a state which is initial if init is True, and terminal if term is True.
DFAState[q, ...][a] gives the transition \[Delta](q, a)";
DFAState::invtr = "Transition `1` is not defined for state `2`.";
DFAState[id_, d_Association, ___][a_] :=
    Lookup[d, Key[a], (Message[DFAState::invtr, a, id]; Undefined)];
DFAState /: MakeBoxes[s : DFAState[_, _?AssociationQ, ___],
  form : (StandardForm | TraditionalForm)] :=
    makeStateSummaryBoxes[s, form];
DFAState /: Keys[DFAState[_, d_, ___]] := Keys[d];
DFAState /: Values[DFAState[_, d_, ___]] := Values[d];


DFAQ::usage = "DFAQ[x] returns True if x is a valid DFA.";
DFAQ[DFA[_?dfaAscQ]] = True;
DFAQ[G_Graph] := DFAQ[AnnotationValue[G, "Automaton"]];
DFAQ[_] = False;


DFA::usage = "DFA[states, alphabet, initial, final] represents a DFA";
DFA::invsym = "The alphabet of `1` does not contain the symbol `2`.";
DFA::invsyms = "The alphabet of `1` does not contain the symbols `2`.";
DFA::missingtr = "Missing definition for transition \[Delta](`1`,`2`).";
DFA::invtrsym = "Unrecognized transition symbol `1` given for state `2`.";
DFA::invprod = "Unrecognized state `1` produced in transition \[Delta](`2`,`3`).";
DFA::invinit = "Unrecognized initial state `1`";
DFA::invterm = "Unrecognized terminal state `1`";
DFA::badcast = "Cannot automatically convert NFA `1` to DFA. Use ToDFA for subset construction.";
DFA::badinit = "Initial states parameter `1` is not a list of length 1.";

DFA[a___, "states" -> states : {_DFAState ..}, b___] :=
    DFA[a, "states" -> GroupBy[states, StateID, First], b];

DFA[OrderlessPatternSequence[
  "states" -> states : <|(_ -> _DFAState) ..|>,
  "initial" -> initial_?validDFAInitQ,
  "terminal" -> terminal_List,
  Optional["alphabet" -> alphabet_List, "alphabet" -> Automatic]]] :=

    DFA[Association @@ {
      "states" -> states,
      "initial" -> initial,
      "terminal" -> terminal,
      "alphabet" -> autoAlt[alphabet, Union @@ (Keys /@ states)]
    }];

DFA[states : {(_ -> {___Rule}) ..}, initial_?validDFAInitQ,
  terminal_List, alphabet_List : Automatic] :=
    Module[{tostate, stateIDs = states[[All, 1]],
      alph = autoAlt[alphabet, Union @@ (Keys@Values@states)]},
      tostate[id_ -> tf_] := With[{symbols = tf[[All, 1]]},
        Scan[If[! MemberQ[symbols, #], Message[DFA::missingtr, id, #]] &,
          alph];
        Scan[Function[
          If[! MemberQ[alph, #[[1]]], Message[DFA::invtrsym, #[[1]], id]];
          If[! MemberQ[stateIDs, #[[2]]],
            Message[DFA::invprod, #[[2]], id, #[[1]]]]],
          tf];
        id ->
            DFAState[id,
              Association[tf], {MemberQ[initial, id],
              MemberQ[terminal, id]}]];
      Scan[If[! MemberQ[stateIDs, #], Message[DFA::invinit, #]] &,
        initial];
      Scan[If[! MemberQ[stateIDs, #], Message[DFA::invterm, #]] &,
        terminal];
      DFA[
        "states" -> KeySort@Association[tostate /@ states],
        "initial" -> initial,
        "terminal" -> terminal,
        "alphabet" -> alph
      ]];

DFA[states : {(_ -> {___}) ..}, alphabet_List, rest__] :=
    DFA[states /. (id_ -> x_List) :> (id -> Thread[alphabet -> x]),
      rest, alphabet];

DFA[dfa_DFA] := dfa;
DFA[nfa_NFA] /; Message[DFA::badcast, nfa] = None;
DFA[g_Graph] := DFA[PureAutomaton[g]];

DFA /: MakeBoxes[dfa : DFA[asc_?dfaAscQ],
  form : (StandardForm | TraditionalForm)] :=
    makeAutomatonSummaryBoxes[dfa, form];
DFA /: Graph[dfa_DFA?DFAQ, opts : OptionsPattern[{Graph, automatonGraph}]] :=
    Annotate[automatonGraph[dfa, opts], "Automaton" -> dfa];
DFA /: Graph3D[dfa_DFA?DFAQ, opts : OptionsPattern[{Graph3D, Graph, automatonGraph}]] :=
    Annotate[
      Graph3D[automatonGraph[dfa, filterOpts[{opts}, {Graph, automatonGraph}, Graph3D]],
        filterOpts[{opts}, Graph3D],
        (*        Lighting -> "Neutral",*)
        EdgeShapeFunction -> GraphElementData[{"Arrow", "ArrowSize" -> 0.015}]],
      "Automaton" -> dfa];
DFA /: ToRules[dfa_DFA?DFAQ] :=
    Normal[Normal@*Transitions /@ States@dfa];

(dfa_DFA?DFAQ)[w_List] /; validDFAInputQ[dfa, w] :=
    With[{Q = States[dfa]},
      MemberQ[IDs[dfa, "Terminal"],
        Fold[Q[#1]@#2 &, First@IDs[dfa, "Initial"], w]]];
(dfa_DFA?DFAQ)[w_List, All] /; validDFAInputQ[dfa, w] :=
    With[{Q = States[dfa]},
      FoldList[Q[#1]@#2 &, First@IDs[dfa, "Initial"], w]];
(dfa_DFA?DFAQ)[w_List, n_Integer?NonNegative] := dfa[Take[w, n], All];
(dfa_DFA?DFAQ)[w_List, n_] := Take[dfa[w, All], n];
(dfa_DFA?DFAQ)[w_String, args___] := dfa[Characters[w], args];


RandomDFA::usage = "RandomDFA[n,k] gives a random DFA with n states on an alphabet of k symbols.";
OprufferDecode[code_] := Module[
  {deg = Lookup[Counts[code] + 1, Range[Length@code + 2], 1]},
  Join[aside[deg[[#]]--&] /@ {First@FirstPosition[deg, 1], #}& /@ code,
    Flatten[Position[deg, 1, {1}, 2, Heads -> False], {2}]]];ptions[RandomDFA] = {
  TerminalStates -> 0.3,
  AlphabetFunction -> Automatic,
  StatesFunction -> Automatic,
  AllStatesReachable -> False};
RandomDFA[statesin : (_Integer | _List), alphin : (_Integer | _List), OptionsPattern[RandomDFA]] :=
    With[{n = unless[statesin, _List, Length@statesin],
      k = unless[alphin, _List, List@alphin]},
      With[{
        nterm = intProp[OptionValue[TerminalStates], n],
        ids = unless[statesin, _Integer, makeStateIDs[n, OptionValue[StatesFunction]]],
        alph = unless[alphin, _Integer, makeAlphabet[k, OptionValue[AlphabetFunction]]]},
        If[OptionValue[AllStatesReachable],
          If[k == 1,
            With[{rs = RandomSample@ids ~ Append ~ RandomChoice[ids]},
              DFA[BlockMap[(First@# -> Rest@#)&, rs, 2, 1],
                alph,
                {First@rs},
                RandomSample[ids, UpTo[nterm]]
              ]],
            With[{asc = GroupBy[prufferDecode@randomPrufferCode[n, k], Last -> First],
              idxs = AssociationThread[Range[n] -> RandomSample@ids]},
              DFA[
                Table[With[{egg = Lookup[asc, i, {}]},
                  i -> RandomSample@Flatten@Join[egg, RandomChoice[;; n, k - Length@egg]]],
                  {i, n}] /. idxs,
                alph,
                {idxs[n]},
                RandomSample[ids, UpTo[nterm]]]]],
          DFA[Thread[ids -> RandomChoice[ids, {Length@ids, Length@alph}]],
            alph,
            RandomSample[ids, 1],
            RandomSample[ids, UpTo[nterm]]]
        ]]];


prufferDecode[code_] := Module[
  {deg = Lookup[Counts[code] + 1, Range[Length@code + 2], 1]},
  Append[(deg[[#]]--; #)& /@ {First@FirstPosition[deg, 1], #}& /@ code,
    Flatten@Position[deg, 1, {1}, 2, Heads -> False]]];


randomPrufferCode[n_, k_] := Which[
  n <= 2, {},
  k == 1, RandomSample[;; n, n - 2],
  n - 2 <= k, RandomChoice[;; n, n - 2],
  True, With[{q = Echo@Quotient[n - 2, k - 1]},
    RandomSample@Flatten@{
      Table[RandomSample[;; n, q], k - 2],
      RandomSample[;; n, q + Mod[n - 2, k - 1]]}
  ]];


FactorDFA::usage = "FactorDFA[n] returns a DFA accepting lists of digits whose decimal value is divisible by n
FactorDFA[n, True] returns a DFA accepting lists of digits whose decimal value is divisible by n, as well as the empty list.";
FactorDFA[n_, acceptEmpty_ : False] := DFA[
  Table[k -> (Mod[10 k + #, n] & /@ Range[0, 9]), {k, 0, n - 1}
  ] ~ Join ~ If[acceptEmpty, {}, {"start" -> (Mod[#, n] & /@ Range[0, 9])}],
  Range[0, 9], {If[acceptEmpty, 0, "start"]}, {0}];


ToDFA::usage = "ToDFA[A] converts the automaton A into an equivalent DFA.
ToDFA[regex] converts a regular expression into a DFA by way of an intermediate NFA.";
Options[ToDFA] = {Method -> Automatic};
ToDFA[regex_?RegexQ] := ToDFA[ToNFA[regex]];
ToDFA[dfa_?DFAQ, OptionsPattern[]] := Switch[
  validatedMethod[OptionValue[Method],
    {Automatic, "Subset", "Indexed", "Minimal"}, ToDFA],
  Automatic, PureAutomaton[dfa],
  "Indexed", ReindexAutomaton[dfa],
  "Subset", RenameStates[dfa, List],
  "Minimal", MinimizeDFA[dfa]];
ToDFA[nfa_?NFAQ, alphabet_List : Automatic, OptionsPattern[]] :=
    With[{init = EpsilonClosure[nfa],
      alph = autoAlt[alphabet, DeleteCases[Alphabet[nfa], EmptyString]],
      method = validatedMethod[OptionValue[Method], {Automatic, "Subset", "Indexed", "Minimal"}, ToDFA]},
      Module[{states = States[nfa], i = 1, initfn = MatchQ[init], termfn, namefn, convert},
        termfn = sowPredicate[ContainsAny[IDs[nfa, "Terminal"]] -> convert, "terminal"];
        namefn = Switch[method, Automatic | "Indexed" | "Minimal", (i++) &, "Subset", Identity];
        convert[subset_] := With[{name = (convert[subset] = namefn@subset)},
          Sow[name -> DFAState[name,
            AssociationMap[
              convert@EpsilonClosure[
                Union @@ Transitions[Lookup[states, subset, Nothing], Key[#], {}],
                states] &,
              alph],
            Through[{initfn, termfn}[subset]]], "states"];
          name];
        With[{harvest = Reap[convert[init], {"states", "terminal"}]},
          DFA[
            "states" -> Association @@ First[harvest[[2, 1]], {}],
            "initial" -> {First[harvest]},
            "terminal" -> Last[harvest[[2, 2]], {}],
            "alphabet" -> alph
          ]] // If[method === "Minimal", MinimizeDFA, Identity]]];


Options[MinimizeDFA] = {Method -> Automatic};
MinimizeDFA::usage = "MinimizeDFA[dfa] returns an equivalent DFA with the minimum number of states.";
MinimizeDFA[dfa_?DFAQ, OptionsPattern[]] :=
    With[{smalldfa = DeleteUnreachableStates[dfa]},
      Module[{newid, newinit, i = 2},
        With[{classes = StatesPartition@smalldfa,
          initQ = MemberQ[First@IDs[smalldfa, "Initial"]]},
          Scan[
            Switch[validatedMethod[OptionValue[Method],
              {Automatic, "Subset", "Indexed"}, MinimizeDFA],
              Automatic | "Indexed", (newid[Alternatives @@ #] = If[initQ[#], newinit = 1, i++]) &,
              "Subset", (newid[Alternatives @@ #] = If[initQ[#], newinit = #, #]) &],
            classes];
          DFA[
            "states" -> Association @@ (
              updateStateRule[#, newid, {newid@StateID@# === newinit, TerminalQ@#}] &
                  /@ Lookup[States@smalldfa, classes[[All, 1]]]),
            "initial" -> {newinit},
            "terminal" -> Union[newid /@ IDs[smalldfa, "Terminal"]], (* Sort and remove duplicates *)
            "alphabet" -> Alphabet[smalldfa]
          ]]]];

(* ::Subsection:: *)
(* Package scope *)

dfaAscQ::usage = "dfaAscQ[asc] returns True if asc is a valid association where asc[\"states\"] is an association, asc[\"initial\"] is a list of length 1, and asc[\"terminal\"] and asc[\"alphabet\"] are both lists.";
dfaAscQ[KeyValuePattern[{"states" -> _Association, "initial" -> {_}, "terminal" -> _List, "alphabet" -> _List}]] = True;
dfaAscQ[_] = False;


productDFA::usage = "productDFA[A1, A2, ..., init, predicate] returns the product DFA with initial state init and terminal states selected by predicate";
productDFA[automata__, init_, termpred_] :=
    Module[{states, terms},
      {states, terms} = Reap[productStates[automata, sowPredicate[termpred -> StateID, "terminal"]], "terminal"];
      DFA["states" -> states,
        "initial" -> init,
        "terminal" -> First[terms, {}],
        "alphabet" -> Alphabet /@ Unevaluated[Intersection[automata]]]];


scanProductDFA::usage = "scanProductDFA[f, A1, A2] applies f to the id of each reachable state in product DFA of A1 and A2, without explicitly constructing it.";
scanProductDFA[f_, dfa1_?DFAQ, dfa2_?DFAQ] := With[
  {queue = CreateDataStructure[
    "Queue", {Catenate@IDs[{dfa1, dfa2}, "Initial"]}],
    statesAscs = States[{dfa1, dfa2}],
    alph = If[! SameAlphabetQ[dfa1, dfa2], Return[False], Alphabet[dfa1]]},
  Module[{enqueue},
    enqueue[tuple_] := (queue["Push", tuple]; enqueue[tuple] = Null);
    While[! queue["EmptyQ"],
      With[{tup = MapThread[Construct,
        {statesAscs, aside[f, queue["Pop"]]}]},
        Scan[enqueue[Transitions[tup, #]] &, alph]]]]
];
scanProductDFA[f_, nfa1_?NFAQ, nfa2_?NFAQ] := With[
  {queue = CreateDataStructure["Queue", {EpsilonClosure /@ {nfa1, nfa2}}],
    statesAscs = States[{nfa1, nfa2}],
    alph = DeleteCases[Alphabet /@ Unevaluated@Union[nfa1, nfa2], EmptyString]},
  Module[{enqueue},
    enqueue[tuple_] := (queue["Push", tuple]; enqueue[tuple] = Null);
    While[! queue["EmptyQ"],
      With[{tup = MapThread[Lookup, {statesAscs, aside[f, queue["Pop"]]}]},
        Scan[enqueue[MapThread[EpsilonClosure,
          {OperatorApplied[Lookup, {3, 1, 2}][#, {}]
              /@ (mergeTransitions /@ tup), statesAscs}]] &,
          alph]]]]
];
scanProductDFA[f_, A1_?AutomatonQ, A2_?AutomatonQ] := scanProductDFA[f, NFA[A1], NFA[A2]];

(* ::Subsection:: *)
(* Private Functions *)

validDFAInputQ[dfa_, w_] := ContainsOnly[w, Alphabet[dfa]] ||
    With[{badsyms = Complement[w, Alphabet[dfa]]},
      Switch[Length[badsyms],
        1, Message[DFA::invsym, dfa, First@badsyms],
        _, Message[DFA::invsyms, dfa, badsyms]]; False];


validDFAInitQ[{_}] = True;
validDFAInitQ[x_] := (Message[DFA::badinit, x]; False);


productStates[dfas : Repeated[_?DFAQ, {2, Infinity}], terminalPredicate_] :=
    With[{queue = CreateDataStructure["Queue", {Catenate@IDs[{dfas}, "Initial"]}],
      statesAscs = States[{dfas}],
      alph = Alphabet /@ Unevaluated@Intersection[dfas],
      statesTag = CreateUUID["NewStates"]},
      Module[{next, tup, enqueue},
        enqueue[tuple_] := (queue["Push", tuple]; enqueue[tuple] = tuple);
        Association@First[
          Last@Reap[
            While[! queue["EmptyQ"],
              tup = MapThread[Construct, {statesAscs, next = queue["Pop"]}];
              Sow[next -> DFAState[next,
                AssociationMap[enqueue[Transitions[tup, #]] &, alph],
                {AllTrue[tup, InitialQ], terminalPredicate[tup]}],
                statesTag]],
            statesTag], {}]]];
productStates[nfas : Repeated[_?NFAQ, {2, Infinity}], terminalPredicate_] :=
    With[{queue = CreateDataStructure["Queue", {EpsilonClosure /@ {nfas}}],
      statesAscs = States[{nfas}],
      alph = DeleteCases[Alphabet /@ Unevaluated@Union[nfas], EmptyString],
      statesTag = CreateUUID["NewStates"]},
      Module[{next, tup, enqueue},
        enqueue[tuple_] := (queue["Push", tuple]; enqueue[tuple] = tuple);
        Association@First[
          Last@Reap[
            While[! queue["EmptyQ"],
              tup = MapThread[Lookup, {statesAscs, next = queue["Pop"]}];
              Sow[next -> DFAState[next,
                AssociationMap[
                  enqueue[MapThread[EpsilonClosure,
                    {OperatorApplied[Lookup, {3, 1, 2}][#, {}]
                        /@ (mergeTransitions /@ tup),
                      statesAscs}]] &, alph],
                {AllTrue[tup, AnyTrue[InitialQ]],
                  Length@tup > 0 && terminalPredicate[tup]}],
                statesTag]], statesTag], {}]]];
productStates[As : Repeated[_?AutomatonQ, {2, Infinity}], terminalPredicate_] :=
    productStates[Sequence @@ (NFA /@ {As}), terminalPredicate];
