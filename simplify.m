(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* SIMPLIFY THE FORMULAS *)

SimplifyRules := 
	Join[OperatorRules, AbsRule, ExpressionRules, 
		MaxMinRules, EquationRules, InequalityRules];

(* WeakSimplify is used to simplify sub-formula and is 
a tactic in StrongSimplify. *)

WeakSimplify[f_] :=  
	Simplify[f //. SimplifyRules] /.
	RulesFromGiven /. RulesForRelations;


(* Simplification Tactics and their names. *)

SimplifyMethods = {
	{"reduces to", WeakSimplify},
	{"simplify formula using local context", SimplifyUsingContext},
	{"check denominators", CheckSoundness}, 
	{"calculate summations with Gosper's Algorithm", SimplifySummation[1]},
	{"calculate summations", SimplifySummation[2]},
	{"simplify summations", SimplifySummation[3]},
	{"simplify products", SimplifyProduct},
	{"simplify limits", SimplifyLimit}};


(* Used to print out the simplification steps. *)

RecordChange[message_, old_, new_] := (
	If[old =!= new, AppendTo[SimplifyMessage, {message, old}]]; new);


(* Try each of the simplification tactics. *)

TrySimplifyMethods[{}, f_] := f;

TrySimplifyMethods[{{message_, function_}, rest___}, f_] :=
	TrySimplifyMethods[{rest}, RecordChange[message, f, function[f]]];


(* Repeatedly try simplification tactics until a fixed point is
reached. *)

StrongSimplify[f_] := (
	SimplifyMessage = {};
	FixedPoint[TrySimplifyMethods[SimplifyMethods, #]&, f]);


(* Simplify formulas using local context. *)

SimplifyUsingContext[or[a_, b__]] := 
	UsingContext[Map[SimplifyUsingContext, or[a, b]]];

SimplifyUsingContext[and[a_, b__]] := 
	UsingContext[Map[SimplifyUsingContext, and[a, b]]];

SimplifyUsingContext[imp[a_, b_]] := 
	UsingContext[Map[SimplifyUsingContext, imp[a, b]]];

SimplifyUsingContext[seq[a_, b_]] := 
	UsingContext[Map[SimplifyUsingContext, seq[a, b]]];

SimplifyUsingContext[f_] := f;


(* Simplify a sub-formula using information provided by its
context. *)

UsingContext[and[a_, b__]] := SimplifyAnd[True, and[a, b]];

UsingContext[or[a_, b__]] := SimplifyOr[False, or[a, b]];

UsingContext[imp[a_, b_]] := (imp[AssumeFalse[#, a], #]&) [AssumeTrue[a, b]];

UsingContext[seq[a_, b_]] := (seq[AssumeFalse[#, a], #]&) [AssumeTrue[a, b]];

UsingContext[f_] := f;



(* Use each conjunct to simplify the remainder of the conjunction. *)

SimplifyAnd[f1_, and[a_, b__]] := 
	SimplifyAnd[and[AssumeTrue[a, f1], a], AssumeTrue[a, and[b]]];

SimplifyAnd[f1_, a_] := and[AssumeTrue[a, f1], a];


(* Use each disjunct to simplify the remainder of the disjunction. *)

SimplifyOr[f1_, or[a_, b__]] := 
	SimplifyOr[or[AssumeFalse[a, f1], a], AssumeFalse[a, or[b]]];

SimplifyOr[f1_, a_] := 
	or[AssumeFalse[a, f1], a];


(* Simplify the second argument assuming the first argument is true. *)

AssumeTrue[h_, f_] :=  f /. RulesFrom[h];


(* Simplify the second argument assuming the first argument is false. *)

AssumeFalse[h_, f_] :=  f /. RulesFrom[not[h]];


(* Extract simplicification rules from a formula. *)


(* Rules come from equations and inequalities. *)

(* In the following rules, if (a-b) - (x-y) === 0, then a==b is equivalent
to x==y, a<=b is equivalent to x<=y, etc. If (a-b) + (x-y) === 0, then
a==b is equivalent to y==x, a<=b is equivalent y<=x, etc. *)

(* If a == b, then a<=b, b<=a and a==b are all true, while a<b and b<a
are false. *)

RulesFrom[a_==b_] := 
	{(x_ <= y_) :> True /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0,
	 (x_ < y_) :> False /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0,
	 (x_ == y_) :> True /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0};

(* If a < b, then a<=b and a<b are both true, while b<a, b<=a, a==b
and b == a are all false. *)

RulesFrom[a_ < b_] :=
	{(x_ <= y_) :> True  /; (a-b) - (x-y) === 0,
	 (x_ <= y_) :> False /; (a-b) + (x-y) === 0,
	 (x_ <  y_) :> True  /; (a-b) - (x-y) === 0,
	 (x_ <  y_) :> False /; (a-b) + (x-y) === 0,
	 (x_ == y_) :> False /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0};

(* If a<=b, then a<=b is true, b<=a is equivalent to a == b, 
a<b equivalent a!=b and b<a is false. *)

RulesFrom[a_ <= b_] :=
	{(x_ <= y_) :> True  /; (a-b) - (x-y) === 0,
	 (x_ <= y_) :> (x == y) /; (a-b) + (x-y) === 0,
	 (x_ <  y_) :> not[x == y] /; (a-b) - (x-y) === 0,
	 (x_ <  y_) :> False /; (a-b) + (x-y) === 0};

(* If a!=b, then a==b and b==a are both false, a <= b is equivalent to a<b
and b<=a is equivalent to b<a. *)

RulesFrom[not[a_ == b_]] :=
	{(x_ == y_) :> False /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0,
	 (x_ <= y_) :> (x < y) /; (a-b) - (x-y) === 0 || (a-b) + (x-y) === 0};


(* If and[a, b], then a and b are both true. *)

RulesFrom[and[a_, b__]] := Union[RulesFrom[a], RulesFrom[and[b]]];


(* Don't use Complicated formulas as simplifying rules. *)

RulesFrom[imp[__]] := {};

RulesFrom[or[a_, b__]] := {};


(* Other kinds of formulas. *)

RulesFrom[not[f_]] := { f -> False };

RulesFrom[h1_] := {h1->True};


(* If the first expression is difference from the second, simplify it. *)

SimplifyIfChanged[f1_, f2_] := If[f1 =!= f2, StrongSimplify[f2], f2];


(* For each appearance of a/b, justify it by proving b!=0 *)

CheckSoundness[s_] := 
	If[FreeQ[s, over], s, WeakSimplify[AddSoundnessConstraint[s, 1]]];


(* If position is 1, the subformula is within an even number of negations;
otherwise it is -1. *)

AddSoundnessConstraint[seq[h_, c_], position_] :=
	seq[AddSoundnessConstraint[h, -position], 
	    AddSoundnessConstraint[c, position]];

AddSoundnessConstraint[imp[h_, c_], position_] :=
	imp[AddSoundnessConstraint[h, -position], 
	    AddSoundnessConstraint[c, position]];

AddSoundnessConstraint[or[a_, b__], position_] :=
	Map[AddSoundnessConstraint[#, position]&, or[a, b]];

AddSoundnessConstraint[and[a_, b__], position_] :=
	Map[AddSoundnessConstraint[#, position]&, and[a, b]];

(* The soundness constraint for an atomic formula is the conjunction
of constraints for each of the quotients within the formula. *)

(* If the atomic formula is within even number of negations, the
soundness constraint is put as an additional conclusion to be proved. *)

AddSoundnessConstraint[f_, 1] :=
	If[FreeQ[f, over], f,
		and[Apply[and, Map[Soundness[f], Position[f, _over]]], f]
			//. over[a_, b_] :> a/b];

(* If the atomic formula is within odd number of negations, the
soundness constraint becomes a prerequisite for the truth of f. *)

AddSoundnessConstraint[f_, -1] :=
	If[FreeQ[f, over], f,
		imp[Apply[and, Map[Soundness[f], Position[f, _over]]], f]
			//. over[a_, b_] :> a/b];

(* The constraint for quotient is that the denominator is not zero. *)

Soundness[f_][{a__}] := (not[f[[a]][[2]] == 0]);


