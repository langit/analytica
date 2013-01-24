(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* THE PACKAGE FOR EQUATIONS *)



BeginPackage["equation`", "UserInterface`", "SystemInterface`"]

(*  Function needed in other package but not
    available to the user:

	EquationRules (equation_rules.m)

	SovleEquation (solve.m)

	SubstEquation (substitution.m)

*)

Begin["EqPrivate`"]

<<equation_rules.m;

<<solve.m;

<<substitution.m;

End[]

EndPackage[]

