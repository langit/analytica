(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* THE PACKAGE FOR TYPES *)

BeginPackage["types`", "UserInterface`", "SystemInterface`"]

(*  Functions provided to user:

	integer (integer.m)

	Divisible (integer.m)

	Even (integer.m)

	Odd (integer.m)

	real (reals.m)

	complex (complexes.m)

	Rpart (complexes.m)

	Ipart (complexes.m)

	i (complexes.m)
*)

Begin["TypePrivate`"]

<<integer.m;

<<complexes.m;

<<reals.m;

End[]

EndPackage[]
