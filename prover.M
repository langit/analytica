(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* THE PACKAGE CONTAINS THE MAIN ROUTINE OF ANALYTICA *)



BeginPackage["prover`", "UserInterface`", "SystemInterface`"]

(* Functions provided to the user:

	Prove (imply.m)

	ProveByInduction (imply.m)

	TeXOn (print.m)

	SuccessStepsOnly (print.m)

	EndDocument (print.m)

	Abbreviate (print.m)

	PrintAbbreviation (print.m)

	PrintGiven (print.m)

	PrintDefinition (print.m)

   Functions needed in other packages but not
   available to the user:

	BranchStack (imply.m)

	TryOtherBranches (imply.m)

	orelse (imply.m)

	TryProving (imply.m)

	FalseQ (imply.m)

	PrintMessage (print.m)

	PrintResult (print.m)

	PrintSequent (print.m)

	PrintLemma (print.m)

	print (print.m)

	SucceedWith (print.m)

*)

Begin["ProverPrivate`"]

<<imply.m;

<<print.m;

<<induction.m;


End[]

EndPackage[]

