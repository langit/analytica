(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* CALCULATING THE UPPER AND LOWER BOUNDS FOR EXPRESSIONS *)


(* try to find the upper bounds of an expression *)

Upper[a_?NumberQ] := If[a<0, {Strict[0]}, {}];

(* the upper bounds of an expression is the union of its given upper bounds
   and the lower bounds calulated from its structure *)

Upper[f_] := UpperOf[f, TermNumber[f]];

(* if the upper bounds of "f" is known, return with it, otherwise calculate
   them *)

UpperOf[f_, n_] := (
	If[KnownUpper[[n]] =!= Unknown, Return[KnownUpper[[n]]]];
	KnownUpper[[n]] = 
		Union[GivenUpper[n], Map[Simplify, CalculateUpper[f]]]);


(* try to find the lower bounds of an expression *)

Lower[a_?NumberQ] := If[a>0, {Strict[0]}, {}];

(* the lower bounds of an expression is the union of its given lower bounds
   and the lower bounds calulated from its structure *)

Lower[f_] := LowerOf[f, TermNumber[f]];

(* if the lower bounds of "f" is known, return with it, otherwise calculate
   them *)

LowerOf[f_, n_] := (
	If[KnownLower[[n]] =!= Unknown, Return[KnownLower[[n]]]];
	KnownLower[[n]] = 
		Union[GivenLower[n], Map[Simplify, CalculateLower[f]]]);



(* Calculate upper bounds for expressions *)

(* Upper bound for additive expression *)

CalculateUpper[a_ + b_] := Join[a+Upper[b], b+Upper[a]];


(* Upper bound of expression with a constant multiple *)

CalculateUpper[c_?NumberQ a_] := If[c>0, c Upper[a], c Lower[a]];


(* Upper bounds for production *)

CalculateUpper[a_ b_] := (
	Join[ If[TrueQ[WeakSimplify[a>=0]], a Upper[b], 
		 If[TrueQ[WeakSimplify[a<=0]], a Lower[b], {}]],
	      If[TrueQ[WeakSimplify[b>=0]], Upper[a] b, 
		 If[TrueQ[WeakSimplify[b<=0]], Lower[a] b, {}]]]);

(* The set of Upper bounds for the absolute value of difference between
   two values of a uniformly continuous function *)

CalculateUpper[Abs[f_[x1_] - f_[x2_]]] :=
	{inverse[delta[f]][Abs[x1 - x2]], Abs[f[x1]] + Abs[f[x2]]} /;
	UniformlyContinuous[f];


(* Upper bound for absolute value of summations *)

CalculateUpper[Abs[a_Plus]] := 
	Map[Abs[a-#] + Abs[#]&, Apply[List, a]];

CalculateUpper[Abs[sum[a_, range_]]] := 
	{sum[Abs[a], range]};


(* Upper bound for summation *)

CalculateUpper[sum[a_, range_]] := -LowerSum[-a, range];


(* Upper Bound for round function *)

CalculateUpper[round[a_]] := {a+1/2};


(* Upper bound for limits *)

CalculateUpper[limit[f_, {v_, v0_}]] := Map[limit[#, {v, v0}]&, Upper[f]];


(* Upper bound for power expressions *)

CalculateUpper[a_ ^ n_Integer] := 
	If[n>0, If[OddQ[n],
		   Upper[a],
		   Upper[WeakSimplify[Abs[a]]]],
		If[OddQ[n],
		   If[TrueQ[WeakSimplify[a>=0]], 
			DeleteZero[Select[Lower[a], WeakSimplify[#>=0]&]], 
			If[TrueQ[WeakSimplify[a<=0]],
				Lower[a], {}]],
		   DeleteZero[Select[Lower[WeakSimplify[Abs[a]]], WeakSimplify[#>0]&]]]] ^ n;

CalculateUpper[a_^n_] :=
	If[TrueQ[WeakSimplify[n<=0]],
		Select[Lower[a], WeakSimplify[Value[#]>0]&] ^n,
		If[TrueQ[WeakSimplify[n>=0]], Upper[a]^n, {}]] /; 
	WeakSimplify[a>=0];


(* Upper bound for minimum *)

CalculateUpper[Min[a_, b__]] := {a, b};


(* Upper bound of absolute value of integrate expression *)

CalculateUpper[Abs[Integrate[a_, range_]]] := 
	Map[Abs[Integrate[#, range]]&, Upper[Abs[a]]];


(* Upper bound for integrate expression *)

CalculateUpper[Integrate[f_, {x_, x1_, x2_}]] :=
	Map[Integrate[#, {x, x1, x2}]&, Upper[f]];


(* Upper bound for bounded functions *)

CalculateUpper[Abs[f_[x__]]] := {Bound[f]} /; Bounded[f];


(* Upper bound for monotonic functions *)

CalculateUpper[f_[x_]] :=
	Join[If[TrueQ[Increasing[f]], Map[f, Upper[x]],
		   If[TrueQ[Decreasing[f]], Map[f, Lower[x]], {}]],
	     If[TrueQ[Bounded[f]], {Bound[f]}, {}]];


(* no upper bounds otherwise *)

CalculateUpper[a_] := {};



(* Calculate lower bounds for expressions *)

(* Lower bounds for addtion *)

CalculateLower[a_ + b_] := Join[a+Lower[b], b+Lower[a]];


(* Lower bound for expression with a constant multiple *)

CalculateLower[c_?NumberQ a_] := If[c>0, c Lower[a], c Upper[a]];


(* Lower bound for summations *)

CalculateLower[sum[a_. Abs[b_], range_]] :=
		{Abs[sum[a b, range]]} /; WeakSimplify[a>=0];

CalculateLower[sum[a_, range_]] := LowerSum[a, range];


(* Lower bounds for absolute value *)

CalculateLower[Abs[a_Plus]] := 
	Prepend[Map[Abs[a-#] - Abs[#]&, Apply[List, a]], 0];

CalculateLower[Abs[a_]] := Join[{0}, Lower[a], -Upper[a]];


(* Lower bound for round function *)

CalculateLower[round[a_]] := {a-1/2};


(* Lower bound for limits *)

CalculateLower[limit[f_, {v_, v0_}]] := Map[limit[#, {v, v0}]&, Lower[f]];


(* Lower bound for production *)

CalculateLower[a_ b_] := (
	Join[ If[TrueQ[WeakSimplify[a>=0]], a Lower[b], 
		 If[TrueQ[WeakSimplify[a<=0]], a Upper[b], {}]],
	      If[TrueQ[WeakSimplify[b>=0]], Lower[a] b, 
		 If[TrueQ[WeakSimplify[b<=0]], Upper[a] b, {}]]]);


(* Lower bound for power expression *)

CalculateLower[a_ ^ n_Integer?EvenQ] := 
	If[n>0, Select[Lower[WeakSimplify[Abs[a]]], WeakSimplify[# >= 0]&], 
		DeleteZero[Select[Upper[WeakSimplify[Abs[a]]], WeakSimplify[# >= 0]&]]]^n;

CalculateLower[a_ ^ n_Integer] :=
	If[EvenQ[n], If[n>0, Upper[a], DeleteZero[Lower[a]]],
		     If[n>0, Lower[a], DeleteZero[Upper[n]]]] ^ n /;
	WeakSimplify[a<0];

CalculateLower[a_ ^ n_] := 
	If[TrueQ[WeakSimplify[n>=0]], 
		Select[Lower[a], WeakSimplify[#>=0]&]^n, 
		If[TrueQ[WeakSimplify[n<=0]], Upper[a]^n, {}]] /; 
	WeakSimplify[a>=0];



(* Lower bound for maximum *)

CalculateLower[Max[a_, b__]] := {a, b};


(* Lower bound for integrate expression *)

CalculateLower[Integrate[f_, {x_, x1_, x2_}]] :=
	Map[Integrate[#, {x, x1, x2}]&, Lower[f]];


(* Lower bound for monotonic function *)

CalculateLower[f_[x_]] :=
	Join[If[TrueQ[Increasing[f]], Map[f, Lower[x]],
		   If[TrueQ[Decreasing[f]], Map[f, Upper[x]], {}]];
	     If[TrueQ[Bounded[f]], {-Bound[f]}, {}]];


(* no lower bound otherwise *)

CalculateLower[a_] := {};



(* delete 0 from a list *)

DeleteZero[{a___, 0, b___}] := DeleteZero[{a, b}];

DeleteZero[{a___, Strict[0], b___}] := DeleteZero[{a, b}];

DeleteZero[a_] := a;



(* lower bound for summations *)

(* The summation of lower bounds is the lower bound of the summation. If 
   no term is negative, the first and last terms are both the lower
   bounds for the summation. *)

LowerSum[a_, {v_, min_, max_}] := EvaluateAssuming[
	and[v>=min, v<=max],
	Join[If[TrueQ[WeakSimplify[and[a>=0, min <= max]]], 
		{a /. v->min, a /. v->max}, {}],
	     Map[sum[#, {v, min, max}]&, Lower[a]]]];


(* if all terms are non-positive, the partial summation is no larger than 
   the total summation *)

LowerSum[a_, {v_, min_, max_, cond_}] := EvaluateAssuming[
	and[v>=min, v<=max, cond],
	Join[If[TrueQ[WeakSimplify[a<=0]], 
		{sum[a, {v, min, max}]},
		{}],
	     Map[sum[#, {v, min, max, cond}]&, Lower[a]]]];


(* the symbol for strict upper or lower bounds, 'S[a]' is an upper or lower
   bound for 'f' means 'a' is a strict upper or lower bound for 'f' *)

Strict/: Strict[a_] <= b_ := a <= b;

Strict/: Strict[a_] < b_ := a <= b;

Strict/: a_ <= Strict[b_] := a <= b;

Strict/: a_ < Strict[b_] := a <= b;

Strict/: Strict[Strict[a_]] := Strict[a];

Strict/: a_ + Strict[b_] := Strict[a + b];

Strict/: a_ Strict[b_] := If[TrueQ[WeakSimplify[or[a>0, a<0]]], Strict[a b], a b];

Strict/: Strict[a_]^b_ := Strict[a^b];

Strict/: Value[Strict[a_]] := a;
