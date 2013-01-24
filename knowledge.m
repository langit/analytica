(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* ADDING LEMMAS, RULES, AND DEFINITIONS TO THE DATA BASE. *)



(* "AddLemma" adds a lemma to the data base.  "Facts" is the conjunction of
   those lemmas which have no hypothesis,  "Lemmas" is the conjunction of 
   those having hypothesis.  Both are grouped with respect to the head of 
   the conclusion. *)



(* Initialize. *)

Facts[_] := True;

Lemmas[_] := True;



(* Add a lemma. Note that quantification may be used in the lemmas. *)



(* Simplify the lemma, rename bound variables. Then add it to the data
base. *)

AddLemma[lemma_] := 
	AddToDataBase[Skolemize[WeakSimplify[lemma], PositivePosition, {}]];



(* Add a lemma to the data base. *)

AddToDataBase[and[a_, b__]] := (AddToDataBase[a]; AddToDataBase[and[b]];);

AddToDataBase[imp[a_, and[b_, c__]]] := 
	(AddToDataBase[imp[a, b]]; AddToDataBase[imp[a, and[c]]];);



(* Add to "Lemmas". *)

AddToDataBase[imp[a_, b_]] := 
	(Lemmas[Head[b]] = and[imp[a, b], Lemmas[Head[b]]];);



(* Add to "Facts". *)

AddToDataBase[a_] := (Facts[Head[a]] = and[a, Facts[Head[a]]];);



(* "UserRules" is a collection of substitution rules, "AddRule" adds a
new rule that comes from an equation which may be quantified. *)



(* Initialize. *)

UserRules = {};

Off[Pattern::rhs];



(* Add a rule, which may have quantified variables in it. Universally
quantified variables "Var[n]" appearing in the rules will be used as
general patterns. *)

AddRule[rule_] := 
	PrependTo[UserRules, GetRule[Skolemize[rule, PositivePosition, {}]]];


(* Unconditional rewrite rule. *)

GetRule[a_ == b_] :=  (a /. Var[n_] :> n_) -> (b /. Var[n_] -> n);


(* Conditional rewrite rules. *)

GetRule[imp[cond_, a_ == b_]] := 
	ConditionalRule[cond /. Var[n_] -> n, a /. Var[n_] -> n_, 
		b /. Var[n_] -> n];

ConditionalRule[cond_, left_, right_] := (left :> right /; WeakSimplify[cond]);



(* Add the definition of a new function to data base. *)



(* Initialize the list of definitions for user defined functions. *)

UserFunctions = {};


(* Add a new definition. *)

AddDefinition[f_ == b_] := AppendTo[UserFunctions, f :> b];

