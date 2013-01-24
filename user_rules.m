(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* USER-DEFINED REWRITE RULES. *)


Rewriting[s_] := Block[{s0, s1}, (

	(* Apply user-defined rewrite rules. *)

	s0 = EvaluateAssuming[not[s], s //. UserRules];

	(* If changed during rewriting, simplify the sequent *)

	s1 = SimplifyIfChanged[s, s0];

	(* If the sequent changed, print it out *)

	If[s1 =!= s, 
		(print["using rewrite rules"]; 
		PrintMessage[SimplifyMessage])];

	Return[s1])];

