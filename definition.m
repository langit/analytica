(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* FUNCTION DEFINITIONS. *)


(* Open definitions. *)

OpenDefinition[s_] := Block[{s0}, (

	(* Open the definition of some functions. *)

	s0 = Skolemize[s /. UserFunctions, NegativePosition, {}];

	(* If the sequent changed, print it out. *)

	If[s0 =!= s, print["open definition"]];

	Return[s0])];

