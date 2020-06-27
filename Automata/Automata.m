(* Mathematica Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: Automata *)
(* :Context: Automata` *)
(* :Author: kvlox *)
(* :Date: 2020-05-12 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 12.1 *)
(* :Copyright: (c) 2020 kvlox *)
(* :Keywords: *)
(* :Discussion: *)

Package["Automata`"]

PackageImport["Developer`"]

PackageExport["StateQ"]
PackageExport["TerminalQ"]
PackageExport["InitialQ"]
PackageExport["AutomatonQ"]
PackageExport["AutomatonGraphQ"]
PackageExport["SameAlphabetQ"]
PackageExport["EmptyAutomatonQ"]
PackageExport["EntireAutomatonQ"]
PackageExport["EquivalentAutomataQ"]
PackageExport["SubsetAutomatonQ"]
PackageExport["EquivalentLanguageQ"]
PackageExport["SubsetLanguageQ"]
PackageExport["PureAutomaton"]
PackageExport["AutomatonType"]
PackageExport["Transitions"]
PackageExport["StateID"]
PackageExport["States"]
PackageExport["IDs"]
PackageExport["StateCount"]
PackageExport["AddTransitions"]
PackageExport["SetInitial"]
PackageExport["SetTerminal"]
PackageExport["RenameStates"]
PackageExport["DeleteUnreachableStates"]
PackageExport["IndexAutomaton"]
PackageExport["ReindexAutomaton"]
PackageExport["TransitiveClosure"]
PackageExport["EpsilonClosure"]
PackageExport["StatesPartition"]
PackageExport["AutomatonComplement"]
PackageExport["AutomatonReversal"]
PackageExport["AutomatonIntersection"]
PackageExport["AutomatonUnion"]
PackageExport["AutomatonSymmetricDifference"]
PackageExport["AutomatonConcatenation"]
PackageExport["AutomatonClosure"]

(* ::Section:: *)
(* Automata *)

(* ::Subsection:: *)
(* Clear Symbols *)
(*
ClearAll[StateQ, TerminalQ, InitialQ, AutomatonQ, AutomatonGraphQ, PureAutomatonQ, SameAlphabetQ, EmptyAutomatonQ,
  EntireAutomatonQ, EquivalentAutomataQ, SubsetAutomatonQ, EquivalentLanguageQ, SubsetLanguageQ, PureAutomaton,
  AutomatonType, Transitions, StateID, States, IDs, StateCount, AddTransitions, SetInitial, SetTerminal, RenameStates,
  DeleteUnreachableStates, IndexAutomaton, ReindexAutomaton, TransitiveClosure, EpsilonClosure, AutomatonReversal,
  AutomatonUnion, AutomatonSymmetricDifference, AutomatonClosure, productStateTerminalPairNoneTrue
];
*)

(* ::Subsection:: *)
(* Symbols *)

EpsilonProbability::usage = "EpsilonProbability is an option for RandomNFA and RandomRegex that specifies the probability a given symbol will be Epsilon.";
TerminalStates::usage = "TerminalStates is an option for RandomNFA and RandomDFA that specifies the number of terminal (accepting) states in the result.";
InitialStates::usage = "InitialStates is an option for RandomNFA that specifies the number of initial states in the result.";
AllStatesReachable::usage = "AllStatesReachable is an option for RandomDFA and RandomNFA that specifies whether to ensure all states in the result are reachable.";
StatesFunction::usage = "StatesFunction is an option for RandomDFA and RandomNFA that specifies the function to use for generating state ids.";
AlphabetFunction::usage = "AlphabetFunction is an option for RandomDFA, RandomNFA, and RandomRegex that specifies the function to use for generating the alphabet of the output.";
Protect[EpsilonProbability, TerminalStates, InitialStates, AllStatesReachable, StatesFunction, AlphabetFunction];

(* ::Subsection:: *)
(* Predicates *)

StateQ::usage = "StateQ[expr] returns True if expr has head NFAState or DFAState";
StateQ[_DFAState | _NFAState] = True;
StateQ[_] = False;


TerminalQ::usage = "TerminalQ[state] gives True if state is a terminal dfa or nfa state.";
TerminalQ[(DFAState | NFAState)[_, _, {_, True}]] = True;
TerminalQ[(DFAState | NFAState)[_, _, True]] = True;
TerminalQ[_] = False;


InitialQ::usage = "InitialQ[state] returns True if state is initial.";
InitialQ[(DFAState | NFAState)[_, _, {True, _}]] = True;
InitialQ[_] = False;


AutomatonQ::usage = "AutomatonQ[A] yields True if A is a valid representation of an automaton.";
AutomatonQ[A_DFA] := DFAQ[A];
AutomatonQ[A_NFA] := NFAQ[A];
AutomatonQ[G_Graph] := AutomatonGraphQ[G];
AutomatonQ[_] = False;


AutomatonGraphQ::usage = "AutomatonGraphQ[G] yields True if G is a graph with a valid \"Automaton\" annotation.";
AutomatonGraphQ[g_Graph] := AutomatonQ[AnnotationValue[g, "Automaton"]];
AutomatonGraphQ[_] = False;


PureAutomatonQ::usage = "PureAutomatonQ[A] returns True if A is a valid Automaton with head NFA or DFA.";
PureAutomatonQ[NFA[_?nfaAscQ] | DFA[_?dfaAscQ]] = True;
PureAutomatonQ[_] = False;


SameAlphabetQ::usage = "SameAlphabetQ[A1, A2, ...] returns true if Alphabet[A1], Alphabet[A2], ... are equivalent as sets.";
SameAlphabetQ[A_] := Quiet[Check[ListQ@Alphabet[A], False]];
SameAlphabetQ[A1_, Ai__] := Quiet[Check[AllTrue[Alphabet /@ {Ai}, ContainsExactly[Alphabet[A1]]], False]];


EmptyAutomatonQ::usage = "EmptyAutomatonQ[A] returns True if A is an automaton whose language an empty set.";
EmptyAutomatonQ[A_?AutomatonQ] :=
    With[{groupfn = If[DFAQ@A, DeleteDuplicates, Apply[Union]],
      states = States@A, terms = IDs[A, "Terminal"]},
      Or[terms === {},
        ! Module[{mark},
          mark[id_] := Or[
            mark[id] = MemberQ[terms, id],
            AnyTrue[groupfn@Values@states@id, mark]];
          AnyTrue[IDs[A, "Initial"], mark]]]];
EmptyAutomatonQ[_] = False;


EntireAutomatonQ::usage = "EntireAutomatonQ[A] yields True if A is an automaton which accepts all strings over its alphabet.";
EntireAutomatonQ[A_?AutomatonQ] := EmptyAutomatonQ[AutomatonComplement[A]];
EntireAutomatonQ[_] = False;


EquivalentAutomataQ::usage = "EquivalentAutomataQ[A1, A2] is True if A1 and A2 are automata that recognize the same language.
EquivalentAutomata[A_1, A_2, ...] yields true if all A_i are equivalent automata.";
EquivalentAutomataQ[_?AutomatonQ] = True;
EquivalentAutomataQ[A1_?AutomatonQ, A2_?AutomatonQ] := productStateTerminalPairNoneTrue[A1, A2, Xor];
EquivalentAutomataQ[_, _] = False;
EquivalentAutomataQ[Ai : Repeated[_, {3, Infinity}]] := With[
  {m = First@MinimalBy[{Ai}, StateCount]},
  AllTrue[DeleteCases[{Ai}, m], EquivalentAutomataQ[m, #] &]
];


SubsetAutomatonQ::usage = "SubsetAutomatonQ[A1, A2] returns True if the language recognized by automaton A1 is a subset of the language recognized by automaton A2.
SubsetAutomatonQ[A, A_1, A_2, ...] yields True if SubsetAutomaton[A, A_i] is true for all A_i.
SubsetAutomatonQ[A] represents an operator form of SubsetAutomatonQ that can be applied to an expression.";
SubsetAutomatonQ[A1_?AutomatonQ, A2_?AutomatonQ] := productStateTerminalPairNoneTrue[A1, A2, {#1 && ! #2} &];
SubsetAutomatonQ[_, _] = False;
SubsetAutomatonQ[A1_][A2_] := SubsetAutomatonQ[A1, A2];
SubsetAutomatonQ[A_, Ai : Repeated[_, {2, Infinity}]] := AllTrue[{Ai}, SubsetAutomatonQ[A]];


EquivalentLanguageQ::usage = "EquivalentLanguageQ[L_1, L_2, ...] returns True if all L_i are automata or regular expressions that describe the same language.";
EquivalentLanguageQ[L__] := EquivalentAutomataQ @@ Replace[{L}, r_?RegexQ :> ToNFA[r], {1}];


SubsetLanguageQ::usage = "SubsetLanguageQ[L1, L2] yields True if the language recognized by automaton or regular expression L1 is a subset of the language recognized by L2.
SubsetLanguageQ[L, L_1, L_2, ...] returns True if SubsetLanguageQ[L, L_i] is True for all L_i.
SubsetLanguageQ[L] represents an operator form of SubsetLanguageQ that can be applied to an expression. ";
SubsetLanguageQ[L_, Li__] := SubsetAutomatonQ @@ Replace[{L, Li}, r_?RegexQ :> ToNFA[r], {1}];
SubsetLanguageQ[L_?RegexQ] := SubsetLanguageQ[ToNFA[L]];
SubsetLanguageQ[L_][Li__] := SubsetLanguageQ[L, Li];


(* ::Subsection:: *)
(* Accessors *)

PureAutomaton::usage = "PureAutomaton[A] returns A as an automaton with head NFA or DFA.";
PureAutomaton[A : (_NFA | _DFA)] := A;
PureAutomaton[g_] := when[AnnotationValue[g, "Automaton"], _?PureAutomatonQ,
  Message[PureAutomaton::inv, HoldForm[PureAutomaton[g]], g,
    "Automaton"]; $Failed];


AutomatonType::usage = "AutomatonType[A] returns NFA if A is an NFA, or DFA if A is a DFA.";
AutomatonType[A_?AutomatonQ] := Head@PureAutomaton[A];


Transitions::usage = "Transitions[dfastate] gives the transition table for a dfa state as the association <|a_1 -> q_1, ...|>, where a_i is a character in the input alphabet, and q_i is the id of \[Delta](dfastate, a_i)].
Transitions[nfastate] gives the transition table for an nfa state as the association <|a_1 -> list_i, ...|>, where a_i is a character in the input alphabet, and list_i is the list {q_1, q_2, ...} of state ids corresponding to \[Delta](nfastate, a_i)].
Transitions[q, spec...] is equivalent to Lookup[Transitions[q], spec...] if q is an explicit DFA or NFA state.
Transitions[{q_1, q_2, ...}, spec...] is equivalent to Lookup[{Transitions[q_1], Transitions[q_2], ...}, spec...], provided all q_i have head NFAState, or all q_i have head DFAState.";
Transitions[(DFAState | NFAState)[_, d_, ___]] := d;
Transitions[(DFAState | NFAState)[_, d_, ___], rest__] := Lookup[d, rest];
Transitions[states : {___DFAState | ___NFAState}, rest__] := Lookup[states[[All, 2]], rest];


StateID::usage = "StateID[q] returns the id of q, where q is an expression with head NFAState or DFAState.";
SetAttributes[StateID, Listable];
StateID[(DFAState | NFAState)[id_, _, ___]] := id;


StateSuccessors::usage = "StateSuccessors[q] returns a list of IDs comprising the set of states to which q has an outgoing transition.
StateSuccessors[q, {a_1, a_2, ...}] returns the set of states to which q has an outgoing transition on one of the symbols a_i.";
StateSuccessors[NFAState[_, d_, ___], (All | PatternSequence[])] := Union @@ Values@d;
StateSuccessors[NFAState[_, d_, ___], symbols_List] := Union @@ Lookup[d, symbols, {}];
StateSuccessors[DFAState[_, d_, ___], (All | PatternSequence[])] := DeleteDuplicates@Values@d;
StateSuccessors[DFAState[_, d_, ___], symbols_List] := DeleteDuplicates@Lookup[d, symbols];
StateSuccessors[symbols : (_List | All)][s_?StateQ] := StateSuccessors[s, symbols];


States::usage = "States[A] returns an association <|id -> state, ...|> of all states in the DFA or NFA A.
States[A, \"Values\"] returns a list {state_1, state_2, ...} of all states in the DFA or NFA A.
States[A, prop] returns an association <|id -> state, ...|> of states with the property prop. Valid properties include  \"Initial\", \"Terminal\", and \"Nonterminal\".
States[A, prop, \"Values\"] returns a list of states with the property prop.";
SetAttributes[States, Listable];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ]] := asc["states"];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Values"] := Values@asc["states"];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Initial"] := KeyTake[asc["states"], asc["initial"]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Initial", "Values"] := Lookup[asc["states"], asc["initial"]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Terminal"] := KeyTake[asc["states"], asc["terminal"]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Terminal", "Values"] := Lookup[asc["states"], asc["terminal"]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Nonterminal"] :=
    KeyTake[asc["states"], Complement[Keys@asc["states"], asc["terminal"]]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Nonterminal", "Values"] :=
    Lookup[asc["states"], Complement[Keys@asc["states"], asc["terminal"]]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "TransitiveClosure"] :=
    KeyTake[asc["states"], TransitiveClosure[asc["initial"], asc["states"]]];
States[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "TransitiveClosure", "Values"] :=
    Lookup[asc["states"], TransitiveClosure[asc["initial"], asc["states"]]];
States[g_Graph?AutomatonGraphQ, rest___] := States[PureAutomaton[g], rest];


IDs::usage = "IDs[A] returns a list of state names for the DFA or NFA A.
IDs[A, prop] gives the IDs for states with property prop. Valid properties include: \"Initial\", \"Terminal\", and \"Nonterminal\".
IDs[A, \"Index\"] returns an association of state ids and their indices: <|id_1 -> 1, id_2 -> 2 ...|>.";
SetAttributes[IDs, Listable];
IDs[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ]] := Keys@asc["states"];
IDs[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Initial"] := asc["initial"];
IDs[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Terminal"] := asc["terminal"];
IDs[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Nonterminal"] := Complement[Keys@asc["states"], asc["terminal"]];
IDs[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Index"] := First /@ PositionIndex[Keys@asc["states"]];
IDs[g_Graph?AutomatonGraphQ, rest___] := IDs[PureAutomaton[g], rest];


StateCount::usage = "StateCount[A] returns the number of states in the automaton A.
StateCount[A, prop] returns the number of states in A with property prop. Valid properties include: \"Initial\", \"Terminal\", and \"Nonterminal\".";
SetAttributes[StateCount, Listable];
StateCount[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ]] := Length[asc["states"]];
StateCount[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Initial"] := Length[asc["initial"]];
StateCount[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Terminal"] := Length[asc["terminal"]];
StateCount[DFA[asc_?dfaAscQ] | NFA[asc_?nfaAscQ], "Nonterminal"] := Length[asc["states"]] - Length[asc["terminal"]];
StateCount[g_Graph?AutomatonGraphQ, rest___] := StateCount[PureAutomaton[g], rest];


Alphabet::usage <> "\nAlphabet[A] returns the alphabet of automaton A.";
DFA /: Alphabet[DFA[asc_?dfaAscQ]] := asc["alphabet"];
NFA /: Alphabet[NFA[asc_?nfaAscQ]] := asc["alphabet"];
Unprotect[Graph];
Graph /: Alphabet[g_Graph?AutomatonGraphQ] := Alphabet[PureAutomaton[g]];
Protect[Graph];

(* ::Subsection:: *)
(* Mutators *)

AddTransitions::usage = "AddTransitions[nfastate, a -> {q1, q2, ...}] returns an NFAState s where s[a] = Union[nfastate[a], {q1, q2, ...}]
AddTransitions[nfastate, {a1 -> {q1, q2, ...}, ...}] returns an NFAState s with the specified transitions added.
AddTransitions[rules] returns an operator form of AddTransitions. ";
AddTransitions[NFAState[id_, d_, rest___], trns : _Rule | KeyValuePattern[{}]] :=
    NFAState[id, Merge[{d, trns}, Apply[Union]], rest];
AddTransitions[trns : _Rule | KeyValuePattern[{}]] := OperatorApplied[AddTransitions][trns];


SetInitial::usage = "SetInitial[state, bool] returns a copy of state with the property that InitialQ[SetInitial[state, bool]] = bool.
SetInitial[bool] is an operator form of SetInitial that can be applied to states.";
SetInitial[s : (NFAState | DFAState)[_, _], init_] := Append[s, {init, False}];
SetInitial[s : (NFAState | DFAState)[_, _, {_, term_} | term_], init_] := ReplacePart[s, 3 -> {init, term}];
SetInitial[init_][s_] := SetInitial[s, init];


SetTerminal::usage = "SetTerminal[state, bool] returns a copy of state with the property that TerminalQ[SetTerminal[state, bool]] = bool.
SetTerminal[bool] is an operator form of SetTerminal that can be applied to states.";
SetTerminal[s : (NFAState | DFAState)[_, _], term_] := Append[s, {False, term}];
SetTerminal[s : (NFAState | DFAState)[_, _, {init_, _}], term_] := ReplacePart[s, 3 -> {init, term}];
SetTerminal[s : (NFAState | DFAState)[_, _, _], term_] := ReplacePart[s, 3 -> {False, term}];
SetTerminal[term_][s_] := SetTerminal[s, term];


RenameStates::usage = "RenameStates[A, f] returns an automaton isomorphic to A, with states {f[q1], f[q2], ...}, where {q1, q2, ...} are the states of A.";
RenameStates[A_?AutomatonQ, f_] :=
    AutomatonType[A][
      "states" -> Association @@ (updateStateRule[f] /@ States@A),
      "initial" -> f /@ IDs[A, "Initial"],
      "terminal" -> f /@ IDs[A, "Terminal"],
      "alphabet" -> Alphabet[A]
    ];


DeleteUnreachableStates::usage = "DeleteUnreachableStates[A] returns an automaton whose state set is exactly TransitiveClosure[A]";
DeleteUnreachableStates[A_?AutomatonQ] :=
    With[{tc = TransitiveClosure@A},
      If[Length@tc == StateCount@A, A,
        AutomatonType[A][
          "states" -> KeyTake[States@A, tc],
          "initial" -> IDs[A, "Initial"],
          "terminal" -> Intersection[IDs[A, "Terminal"], tc],
          "alphabet" -> Alphabet@A]]];


IndexAutomaton::usage = "IndexAutomaton[A] gives";
IndexAutomaton[A_?AutomatonQ] := RenameStates[A, IDs[A, "Index"]];


ReindexAutomaton::usage = "ReindexAutomaton[A] returns an automaton similar to A, but whose states are renamed with positive integers according to the order each is visited in a depth-first search from the initial states. By default, the returned automaton includes only those states which are reachable from the initial.
IndexAutomaton[A, True] returns the same, but also keeps disconnected components. The resulting automaton is exactly isomorphic to A.";
ReindexAutomaton[A_?AutomatonQ, allComponents_ : False] :=
    Module[{newinits, convert, i = 1, oldstates = States[A],
      newstates = CreateDataStructure["HashTable"]},
      convert[id_] := With[{newid = (convert[id] = i++)},
        newstates["Insert", newid -> updateState[oldstates[id], convert]];
        newid];
      newinits = convert /@ IDs[A, "Initial"];
      While[allComponents,
        convert@First[Complement[Keys@oldstates, specificArguments[convert]], Break[]]];
      With[{states = Normal@newstates},
        AutomatonType[A][
          "states" -> states,
          "initial" -> newinits,
          "terminal" -> (convert[id_] = Nothing; convert /@ IDs[A, "Terminal"]) ,
          "alphabet" -> If[allComponents, Alphabet[A], Union @@ (Keys /@ states)]
        ]]
    ];


ClearAll[TransitiveClosure];
TransitiveClosure::usage = "TransitiveClosure[q, A] returns the transitive closure of state q in automaton A.
TransitiveClosure[{q_1, q_2, ...}, A] returns the union (TransitiveClosure[q_2,A] \[Union] TransitiveClosure[q_2, A] \[Union] ...)
TransitiveClosure[A] returns the transitive closure of the initial states of automaton A.
TransitiveClosure[states, transitions] returns the transitive closure of the given states according to the given transition specifications. The parameter transitions should be an association or list of rules of the form q -> t, where q is a state id, and t is the transition table for q as an association or list of rules.
TransitiveClosure[..., {a_1, a_2, ...}] gives the transitive closure over the set of symbols a_1, a_2, ...";
TransitiveClosure::invstate = "State `1` not found.";
TransitiveClosure[{}, ___] = {};
TransitiveClosure[A_?AutomatonQ, syms_List : All] := TransitiveClosure[IDs[A, "Initial"], States@A, syms];
TransitiveClosure[ids_List, A_?AutomatonQ, syms_List : All] := TransitiveClosure[ids, States@A, syms];
TransitiveClosure[id : Except[_List], rest__] := TransitiveClosure[{id}, rest];
TransitiveClosure[ids_List, rules : {(_ -> _) ...}, syms_List : All] := TransitiveClosure[ids, Association@rules, syms];
TransitiveClosure[ids_List, Q_Association, syms : (_List | All) : All] :=
    Reap[Module[{push},
      With[{
        succs = Which[
          syms === All, Values,
          AllTrue[Q, StateQ], Transitions[#, syms, Nothing] &,
          True, Lookup[#, syms, Nothing] &],
        lvl = Switch[Q, <|(_ -> (_[(_ -> _List) ...] | _NFAState)) ...|>, {2}, _, {1}],
        state = Lookup[Q, Key@#, Message[TransitiveClosure::invstate, #]; {}] &,
        queue = CreateDataStructure["Queue", (push[Sow[#]] = Null; #) & /@ ids]},
        push[id_] := push[Sow[id]] = (queue["Push", id];);
        While[! queue["EmptyQ"],
          Scan[push, succs@state@queue["Pop"], lvl]]]]][[2, 1]];


EpsilonClosure::usage = "EpsilonClosure[A] computes the epsilon closure (that is, the transitive closure over the empty string) of the initial states in the Automaton A.
EpsilonClosure[q, A] gives the epsilon closure of state q in A.
EpsilonClosure[{q_1, q_2, ...}, A] gives EpsilonClosure[q_1, A] \[Union] EpsilonClosure[q_2, A] \[Union] ...
EpsilonClosure[states, transitions] finds the epsilon closure of states in transitions, where transitions can be any transition specification recognized by TransitiveClosure. ";
EpsilonClosure[A_?AutomatonQ] :=
    TransitiveClosure[IDs[A, "Initial"], States@A, {EmptyString}];
EpsilonClosure[states_, transitions_] :=
    TransitiveClosure[states, transitions, {EmptyString}];


StatesPartition::usage = "StatesPartition[dfa] returns a list of partition blocks for the states of dfa, according to the equivalence relation p~q \[DoubleLongLeftRightArrow] For all w\[Element]\!\(\*SuperscriptBox[\(\[CapitalSigma]\), \(*\)]\), \!\(\*OverscriptBox[\(\[Delta]\), \(^\)]\)(p,w) accepts if and only if \!\(\*OverscriptBox[\(\[Delta]\), \(^\)]\)(q,w) accepts";
StatesPartition[dfa_?DFAQ, indices_ : False] :=
    Module[{equivQ},
      equivQ[x_, x_] = True;
      equivQ[___] = False;
      SetAttributes[equivQ, Orderless];
      With[{alph = Alphabet@dfa,
        states = States@dfa,
        partition = CreateDataStructure["DisjointSet", (* Apparently doesn't like packed arrays *)
          Developer`FromPackedArray[Transpose@List@IDs[dfa]]]},
        Scan[Apply[partition["Unify", ##] &],
          FixedPoint[Select[
            (equivQ[Sequence @@ #] = AllTrue[
              Transpose@Lookup[Transitions /@ Lookup[states, #], alph],
              Apply[equivQ]]) &],
            (equivQ[Sequence @@ #] = True; #) &
                /@ Catenate[Subsets[#, {2}] & /@ IDs[dfa, {"Terminal", "Nonterminal"}]]]];
        partition["Subsets"]]] // If[indices, Map[IDs[dfa, "Index"], #, {-1}] &, Identity];


AutomatonComplement::usage = "AutomatonComplement[A] returns a DFA recognizing the complement of the language recognized by A.";
AutomatonComplement[nfa_?NFAQ] := AutomatonComplement[ToDFA[nfa, Method -> "Minimal"]];
AutomatonComplement[dfa_?DFAQ] := DFA[
  "states" -> (updateState[#, Identity, {Automatic, ! TerminalQ[#]}] & /@ States[dfa]),
  "initial" -> IDs[dfa, "Initial"],
  "terminal" -> IDs[dfa, "Nonterminal"],
  "alphabet" -> Alphabet[dfa]];


AutomatonReversal::usage = "AutomatonReversal[A] returns an NFA recognizing the reversal of the language recognized by A.";
AutomatonReversal[A_?AutomatonQ] := NFA[
  Merge[
    Switch[AutomatonType[A],
      NFA, Function[{x, lst}, (Thread[#2 -> {#1 -> x}, List, 1]) & @@@ lst],
      DFA, Function[{x, lst}, (#2 -> {#1 -> x}) & @@@ lst]
    ] @@@ ToRules[PureAutomaton@A],
    Merge[#, Identity] &],
  IDs[A, "Terminal"],
  IDs[A, "Initial"]];


AutomatonIntersection::usage = "AutomatonIntersection[A_1, A_2, ...] returns a DFA for the intersection of the languages recognized by the A_i.";
AutomatonIntersection[A_?AutomatonQ] := A;
AutomatonIntersection[dfas : Repeated[_?DFAQ, {2, Infinity}]] :=
    productDFA[dfas, {Catenate[IDs[{dfas}, "Initial"]]}, AllTrue[TerminalQ]];
AutomatonIntersection[Ai : Repeated[_?AutomatonQ, {2, Infinity}]] :=
    productDFA[Ai, {EpsilonClosure /@ {Ai}}, AllTrue[AnyTrue[TerminalQ]]];


AutomatonUnion::usage = "AutomatonUnion[A_1, A_2, ...] returns a DFA for the union of the languages recognized by the A_i.";
AutomatonUnion[A_?AutomatonQ] := A;
AutomatonUnion[dfas : Repeated[_?DFAQ, {2, Infinity}]] :=
    productDFA[dfas, {Catenate[IDs[{dfas}, "Initial"]]}, AnyTrue[TerminalQ]];
AutomatonUnion[Ai : Repeated[_?AutomatonQ, {2, Infinity}]] :=
    productDFA[Ai, {EpsilonClosure /@ {Ai}}, AnyTrue[AnyTrue[TerminalQ]]];


AutomatonSymmetricDifference::usage = "AutomatonSymmetricDifference[A1, A2] returns a DFA for the symmetric difference of the languages recognized by A1 and A2.";
AutomatonSymmetricDifference[dfas : Repeated[_?DFAQ, {2}]] :=
    productDFA[dfas, {Catenate[IDs[{dfas}, "Initial"]]}, Xor @@ (TerminalQ /@ #) &];
AutomatonSymmetricDifference[Ai : Repeated[_?AutomatonQ, {2}]] :=
    productDFA[Ai, {EpsilonClosure /@ {Ai}}, Xor @@ (AnyTrue[TerminalQ] /@ #) &];


AutomatonConcatenation::usage = "AutomatonConcatenation[A_1, A_2, ...] gives an NFA accepting the concatenation of the languages recognized by the A_i.";
AutomatonConcatenation[Ai : Repeated[_?AutomatonQ, {2, Infinity}]] :=
    With[{nfas = NFA /@ {Ai}, n = Length@{Ai}},
      NFA[
        "states" -> Join @@ MapIndexed[
          Function[{nfa, pos}, With[
            {itrules =
                Switch[pos,
                  {1}, {Automatic, False},
                  {n}, {False, Automatic},
                  _, {False, False}],
              i = First@pos},
            If[i >= n, Association,
              Composition[
                MapAt[AddTransitions[EmptyString -> (Subscript[#, i + 1] & /@ IDs[nfas[[i + 1]], "Initial"])],
                  {Key@Subscript[#, i]}& /@ IDs[nfa, "Terminal"]],
                Association]]@Map[updateStateRule[Subscript[#, i] &, itrules], States[nfa, "Values"]]]],
          nfas],
        "initial" -> Thread[Subscript[IDs[nfas[[1]], "Initial"], 1]],
        "terminal" -> Thread[Subscript[IDs[nfas[[n]], "Terminal"], n]],
        "alphabet" -> Union @@ (Alphabet /@ nfas)]];


AutomatonClosure::usage = "AutomatonClosure[A] returns an NFA for the closure of the language recognized by A with respect to concatenation.";
AutomatonClosure[A_?AutomatonQ] := With[
  {startid = Unique[], terms = IDs[A, "Terminal"],
    critrule = EmptyString -> IDs[A, "Initial"]},
  NFA["states" -> MapAt[
    SetInitial[False],
    MapAt[
      AddTransitions[critrule],
      States@ToNFA[A], List@*Key /@ terms],
    Transpose@{Key /@ IDs[A, "Initial"]}
  ] ~ Append ~ (startid ->
      NFAState[startid, Association@critrule, {True, True}]),
    "initial" -> {startid},
    "terminal" -> terms ~ Append ~ startid,
    "alphabet" -> Union[Alphabet[A], {EmptyString}]]
];


(* ::Subsection:: *)
(* Private Functions *)
productStateTerminalPairNoneTrue[A1_, A2_, pred_] := Module[
  {t1, t2},
  t1[_] = False; Scan[(t1[#] = True) &, IDs[A1, "Terminal"]];
  t2[_] = False; Scan[(t2[#] = True) &, IDs[A2, "Terminal"]];
  Catch[scanProductDFA[
    Apply[If[AutomatonType[A1] === DFA === AutomatonType[A2],
      If[pred[t1[#1], t2[#2]], Throw[False]] &,
      If[pred[AnyTrue[#1, t1], AnyTrue[#2, t2]], Throw[False]] &]],
    A1, A2];
  True]
];

(* TODO: NFA reduction *)
(* TODO: Pushdown Automata *)

