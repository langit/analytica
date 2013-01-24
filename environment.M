(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* PROOF CONTEXT PACKAGE *)



BeginPackage["environment`", "UserInterface`", "SystemInterface`"]

(*   Functions provided to the user:

	Facts (knowledge.m)

	Lemmas (knowledge.m)

	AddLemma (knowledge.m)

	AddRule (knowledge.m)

	AddDefinition (knowledge.m)

	UserRules (knowledge.m)

	CurrentPath (context.m)

	CurrentSection (context.m)

	StartSection (context.m)

	EndSection (context.m)

	Given (context.m)

	GivenTo (context.m)

	Initialize (context.m)

	ProveAndSave (context.m)

	ProveAndSaveTo (context.m)
 
   Functions needed in other packages but not
   available to the user:

	BasicTerms (terms.m)

	NumberOfTerms (terms.m)

	TermNumber (terms.m)

	NumberOfAppearances (terms.m)

	Appearances (terms.m)

	KnownUpper (context.m)

	KnownLower (context.m)

	Unown (context.m)

	GivenEquations (context.m)

	GivenUpper (context.m)

	GivenLower (context.m)

	RulesFromGiven (context.m)

	EvaluateAssuming (context.m)

	GivenFormulas (context.m)

	UserFunctions (knowledge.m)

*)

Begin["EnvPrivate`"]

<<context.m;

<<knowledge.m;

<<terms.m;

End[]

EndPackage[]