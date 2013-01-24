(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)


(*  INEQUALITY PACKAGE *)



BeginPackage["inequality`", "UserInterface`", "SystemInterface`"]

(* Functions provided to the user:

	Upper (bound.m)

	Lower (bound.m)

   Function needed in other package but not
   available to the user:

	ProveUsingBound (usebound.m)

	Strict (bound.m)

	InequalityRules (inequality_rules.m)

*)

Begin["IneqPrivate`"]

<<bound.m;

<<usebound.m;

<<inequality_rules.m;

End[]

EndPackage[]
