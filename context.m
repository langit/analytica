(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* ORGANIZATION OF PROOF CONTEXT *)



(* GivenIdentitiesAt is the conjunction of identities given in a proof 
   section *)

GivenIdentitiesAt[_] := {};


(* RulesGivenIn is the simplify rules comes from the given formulas in a 
   proof section *)

RulesGivenIn[_] := {};

GivenFormulasIn[_] := {};


(* the current context path and the current proof section *)
CurrentPath = {};

CurrentSection := CurrentPath[[1]];


(* change context *)

(* start a new proof section *)

StartSection[] := StartSection[Unique["Temporal"]];

StartSection[a_] := (

	(* reset the known upper and lower bounds *)

	ResetKnownBounds[];


	(* set the current proof context *)

	PrependTo[CurrentPath, a];);


(* end the current proof section *)


EndSection[] :=  (

	(* clear the given upper or lower bounds, which are no longer 
	   useful *)

	clear[GivenUpperAt[CurrentSection], GivenLowerAt[CurrentSection]];
	GivenUpperAt[CurrentSection] =.;
	GivenLowerAt[CurrentSection] =.;

	(* clear the set of given properties *)
	
        RulesGivenIn[CurrentSection] = {};
	GivenIdentitiesAt[CurrentSection] = {};
	

	(* reset the current proof context *)

	CurrentPath = Drop[CurrentPath, 1] ;
	RulesGivenIn[a] = {};


	(* reset the known upper or lower bound *)


	ResetKnownBounds[]; );


ResetKnownBounds[] := (
	KnownUpper = Table[Unknown, {NumberOfTerms}];
	KnownLower = Table[Unknown, {NumberOfTerms}]; );


(* clear the rewrite rules about some functions *)

clear[a___] := Clear[a];



(* EvaluateAssuming tries to calculate "result" assuming "cond" is true *)

SetAttributes[ EvaluateAssuming, HoldRest ];

EvaluateAssuming[True, result_] := result;

EvaluateAssuming[cond_, result_] := Block[{tempresult},

	(* otherwise, start a temporal proof context for it *)

	StartSection[];

	(* make "cond" as given *)

	AddKnowledge[cond, CurrentSection];

	(* calculate "result" under the new context *)

	tempresult = result;

	(* then end the temporal context *)

	EndSection[];

	(* and return with the result *)

	tempresult];



(* save the theorems so that they can be used later *)

(* save to the current section *)

SetAttributes[ProveAndSave, {HoldAll}];

ProveAndSave[form_] := (Prove[form]; Given[form]);

ProveAndSave[form__] := (Prove[and[form]]; Given[form]);

(* save to another section *)


ProveAndSaveTo[form__, a_] := (Prove[and[form]]; GivenTo[and[form], a]);



(* save given formulas in current section *)

Given[a__] := GivenTo[and[a], CurrentSection];


(* save given formulas to some directed section *)

GivenTo[form_, section_] := 
	AddKnowledge[WeakSimplify[form], section];

AddKnowledge[and[a_, b__], section_] := 
	( AddKnowledge[a, section]; AddKnowledge[and[b], section] );

AddKnowledge[form_, section_] := (

	AppendTo[GivenFormulasIn[section], form];

	(* if given a inequality, add some knowledge about the upper or 
	   lower bounds *)

	If[Head[form] == LessEqual,
		AddUpperBound[form[[1]] - form[[2]], 0, section]];

	If[Head[form] == Less,
		AddUpperBound[form[[1]] - form[[2]], Strict[0], section]];

	(* if given a identity, add it to the set of given identities, so
	   it can be used for substitution *)

	If[Head[form]==Equal, 
		AddIdentity[form, section]];

	(* use the given formula as simplify rules *)

	AddSimplifyRules[form, section];);



(* GivenIdentities is the conjunctions of given identities *)

GivenIdentities := Apply[Union, Map[GivenIdentitiesAt, CurrentPath]];


(* RulesFormGiven specifies the simplify rules come from the given 
   knowledge in current proof context *)

RulesFromGiven := Apply[Union, Map[RulesGivenIn, CurrentPath]];

GivenFormulas[] := Apply[Union, Map[GivenFormulasIn, CurrentPath]];


(* the given upper bound for the "n"th basic term *)

GivenUpper[n_] := Apply[Union, Map[(GivenUpperAt[#][n])&, CurrentPath]];


(* the given lower bound for the "n"th basic term *)

GivenLower[n_] := Apply[Union, Map[(GivenLowerAt[#][n])&, CurrentPath]];



(* install the Upper or Lower bounds given in a section *)

GivenUpperAt[section_] := (
	GivenUpperAt[section] = Unique["Upper"];
	GivenUpperAt[section][_] := {}; 
	GivenUpperAt[section]);

GivenLowerAt[section_] := (
	GivenLowerAt[section] = Unique["Lower"];
	GivenLowerAt[section][_] := {}; 
	GivenLowerAt[section]);


(* if "upper" is an upper bound for "f1 + f2", "upper - f2" is an upper 
   bound for "f1" and "upper - f1" is an upper bound for "f2" *)

AddUpperBound[f1_ + f2_, upper_, section_] := (
	AddUpperBound[f1, upper - f2, section];
	AddUpperBound[f2, upper - f1, section]);

(* if "upper" is an upper bound for "n f", if "n > 0", "upper/n" is an 
   upper bound for "f", otherwise "upper/n" is a lower bound for "f" *)

AddUpperBound[n_?NumberQ f_, upper_, section_] :=
	If[n > 0, AddUpperBound[f, upper/n, section],
		  AddLowerBound[f, upper/n, section]];

AddUpperBound[f_ f1_^(n_Integer?Negative e_.), upper_, section_] :=
	AddUpperBound[f, upper f1^(-n e), section] /; 
	EvenQ[n] || WeakSimplify[f1>=0];

AddUpperBound[f_ f1_^(n_Integer?Negative e_.), upper_, section_] :=
	AddLowerBound[f, upper f1^(-n e), section] /; 
	OddQ[n] && WeakSimplify[f1<=0];

(* add "upper" as an extra upper bound for "f" in context "section" *)

AddUpperBound[f_, upper_, section_] := ( 
	If[NumberQ[f] || !FreeQ[upper, f], Return[]];
	ResetKnownBounds[];
	PrependTo[GivenUpperAt[section][TermNumber[f]], upper]);
	

(* if "lower" is a lower bound for "f1 + f2", "lower - f2" is a lower bound 
   for "f1" and "lower - f1" is a lower bound for "f2" *)

AddLowerBound[f1_ + f2_, lower_, section_] := (
	AddLowerBound[f1, lower - f2, section];
	AddLowerBound[f2, lower - f1, section]);

(* if "lower" is a lower bound for "n f", if "n > 0", "lower/n" is a lower
   bound for "f", otherwise "lower/n" is an upper bound for "f" *)

AddLowerBound[n_?NumberQ f_, lower_, section_] :=
	If[n > 0, AddLowerBound[f, lower/n, section],
		  AddUpperBound[f, lower/n, section]];

AddLowerBound[f_ f1_^(n_Integer?Negative e_.), upper_, section_] :=
	AddLowerBound[f, upper f1^(-n e), section] /; 
	EvenQ[n] || WeakSimplify[f1>=0];

AddLowerBound[f_ f1_^(n_Integer?Negative e_.), upper_, section_] :=
	AddUpperBound[f, upper f1^(-n e), section] /;
	OddQ[n] && WeakSimplify[f1<=0];


(* add "lower" as an extra lower bound for "f" in context "section" *)

AddLowerBound[f_, lower_, section_] := (
	If[NumberQ[f] || !FreeQ[lower, f], Return[]];
	ResetKnownBounds[];
	PrependTo[GivenLowerAt[section][TermNumber[f]], lower]);

(* add a identity to the tontext "section" *)

AddIdentity[a_ == b_, section_] :=
	AppendTo[GivenIdentitiesAt[section], a->b];


(* add simplify rules which comes from "form", to the context "section" *)

AddSimplifyRules[form_, section_] :=
       (RulesGivenIn[section] = 
		Union[RulesFrom[form], RulesGivenIn[section]]);


(* initialize the current proof context *)

Initialize[] := (

	(* if the prover is at a temporal context , end it *)

	While[!FreeQ[CurrentPath, Temp], EndSection[]];

	(* clear the set of given properties *)
	
        RulesGivenIn[CurrentSection] = {};
	GivenIdentitiesAt[CurrentSection] = {};
	
	(* clear the set of given upper or lower bounds of expressions *)
	
	clear[GivenUpperAt[CurrentSection], GivenLowerAt[CurrentSection]];
	GivenUpperAt[CurrentSection][_] := {};
	GivenLowerAt[CurrentSection][_] := {};
	
 	(* reset the known upper or lower bound *)

	ResetKnownBounds[];

	(* reset the branch stack *)

	BranchStack = {};
);



