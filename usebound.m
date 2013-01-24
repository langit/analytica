(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

DepthBound = 3;

ProveUsingBound[s_] := (
	If[DepthCount == 0, Bounds[0] = Bounds[1] = Bounds[2] = {}];
	If[DepthCount >= DepthBound, False, TryingUsingBound[False, s]]);

TryingUsingBound[c0_, seq[h_, or[c1_, c2__]]] :=
	orelse[ UsingBound[seq[h, or[c0, c2]], c1], TryingUsingBound[or[c0, c1], seq[h, or[c2]]]];

TryingUsingBound[s0_, seq[and[h1_, h2__], False]] :=
	orelse[ UsingBound[seq[and[h2], s0], not[h1]], TryingUsingBound[seq[h1, s0], seq[and[h2], False]]];

TryingUsingBound[s0_, seq[h_, False]] :=
	UsingBound[s0, not[h]];

TryingUsingBound[c0_, seq[h_, c1_]] := 
	orelse[UsingBound[seq[h, c0], c1], TryingUsingBound[seq[True, or[c0, c1]], seq[h, False]]];

TryingUsingBound[a_, b_] := False;


(* try to prove a sequent by replace expressions appears in inequalities
   by their upper or lower bounds *)

UsingBound[s_, a_ < b_] := 
	UseBound[s, SortingByLength[ EvaluateAssuming[not[s], 
			SimplifyEach[Join[Map[#<b &, Upper[a]],
					  Map[a<# &, Lower[b]]]] /. Strict -> Identity]]];

UsingBound[s_, a_ <= b_] := 
	UseBound[s, SortingByLength[ EvaluateAssuming[not[s], 
			SimplifyEach[Join[Map[#<=b &, Upper[a]],
					  Map[a<=# &, Lower[b]]]] /. Strict -> Identity]]];

UsingBound[__] := False;


SortingByLength[a_List] := 
	Map[a[[#[[2]]]]&, Sorting[Map[LeafCount[#[[3]]]&, a]]];

SortingByLength[a_] := a;

Sorting[a_List] := Sort[Transpose[{a, Range[Length[a]]}]]


DepthCount = 0;


(* proving the inequality after replaced with lower or upper bounds *)

UseBound[s_, {}] := False;

UseBound[s_, True] := (
	PrintResult["replace expression with its lower or upper bounds", True];
	TryOtherBranches[True]);

UseBound[s_, {a___, {_, m_, True}, c___}] := (
	print["replace expression with its lower or upper bounds"];
	PrintMessage[Map[{#[[1]], or[s, #[[2]]]}&, m]]; 
	PrintSequent[True];
	TryOtherBranches[True]);

UseBound[s_, {{_, m_, b1_}}] := Block[{DepthCount = DepthCount + 1}, (
	print["replace expression with its lower or upper bounds"];
	PrintMessage[Map[{#[[1]], or[s, #[[2]]]}&, m]]; 
	SucceedWith[TryProving[or[s, b1]]])];


UseBound[s_, b_] := Block[{DepthCount = DepthCount + 1},

	print["replace expression with its lower or upper bounds"];

	PrintSequent1[or[s, Apply[or, Map[#[[1]]&, b]]]];
	print1["      - - - - - - - A", ToString[DepthCount], "\n"];

	TryEach[s, b]];


(* try to see if one of the disjuncts can be rewritten to true *)

SimplifyEach[{}] := {};

SimplifyEach[{a___, True, b___}] := True;

SimplifyEach[{False, b___}] := SimplifyEach[{b}];

SimplifyEach[{a_, b___}] := 
	If[MemberQ[Bounds[DepthCount], a], 
		SimplifyEach[{b}],
		(AppendTo[Bounds[DepthCount], a]; 
			ff0[a, StrongSimplify[a], {b}])];


ff0[a_, True, b_] := {{a, SimplifyMessage, True}};

ff0[a_, False, b_] := SimplifyEach[b];

ff0[a_, _and, b_] := SimplifyEach[b];

ff0[a_, a1_, b_] := Join[{{a, SimplifyMessage, a1}}, SimplifyEach[b]];



(* try each of the disjuncts in the disjunction coming from introducing
   the lower or upper bound of expression in inequalities *)

(* try disjuncts one by one *)

TryEach[s_, {a_, b__}] := 
	orelse[TryEach[s, {a}], TryEach[s, {b}]];

(* print the label and then try proving the new inequality *)

TryEach[s_, {{_, m_, a1_}}] := (
	print1["part of  \"A", ToString[DepthCount], "\""];
	PrintMessage[Map[{#[[1]], or[s, #[[2]]]}&, m]]; 
	SucceedWith[TryProving[or[s, a1]]]);

