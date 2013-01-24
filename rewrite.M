(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* THE PACKAGE FOR REWRITING FORMULAS *)



BeginPackage["rewrite`", "UserInterface`", "SystemInterface`"]


(* Functions needed in other packages but not
   available to the user:

	OpenDefinition (definition.m)

	Rewriting (user_rules.m)

	Factorize (factorize.m)

*)


Begin["RewritePrivate`"]


<<definition.m;

<<user_rules.m;

<<factorize.m;

End[]

EndPackage[]

