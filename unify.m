(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)


(* UNIFICATION AND SUBSTITUTION FOR VARIABLES *)


(* H1 & ... & Hn --> C1 | ... | Cm  is true if some Cj matches some Hi or 
   some given fact. *)
   


(* Check if one of the disjuncts of the second argument unifies with a 
   conjunct of the first. *)

disjunct[h_, or[a_, b__]] := orelse[disjunct[h, a], disjunct[h, or[b]]];



(* check if "c" matches a conjunct of "h" or some fact similar to "c". *)

disjunct[h_, c_] := 
        orelse[(MatchingState = hypothesis; conjunct[h, c]),  
               (MatchingState = Facts; conjunct[Facts[Head[c]], c ])];
               



(* Check if the second argument matches a conjunct of the first. *)

conjunct[and[a_, b__],  c_] :=  
        orelse[conjunct[a, c],  conjunct[and[b],  c]];

conjunct[h_, c_] :=  Block[{u},
 
        (* If the conclusion matches a fact, set the current lemma. *)

        If[MatchingState === Facts, CurrentLemma = h]; 

        (* If unification fails, return False. *)

        If[FalseQ[u = unify[h, c]], Return[False]];

        (* Otherwise, print out the lemma used and the unifier. *)

        SucceedWith[ 
                If[MatchingState === hypothesis, 
                  PrintResult["matching hypothesis with", u], 
                  (print["matching lemma"]; 
                   PrintLemma[CurrentLemma];
                   PrintResult["with", u])];

                (* Now try to prove other branches of the theorem. *)

                TryOtherBranches[u]]

        ];


(* Check if two formulas unify.  If so, return the substitution. 
If the formulas do not unify, return False. *)

unify[a_, a_] := substitution[];


(* Unification of a variable and a term *)

unify[a_, Var[n_]] :=  
        substitution[{Var[n] -> a}]  /; FreeQ[a, n];

unify[Var[n_], a_] :=  
        substitution[{Var[n] -> a}]  /; FreeQ[a, n];

unify[Var[n_] + a_, 0] :=
        substitution[{Var[n] -> -a}] /; FreeQ[a, n];

unify[-Var[n_] + a_, 0] :=
        substitution[{Var[n] -> a}]  /;  FreeQ[a, n];
        
        
        
(* Unification of atomic formulas *)
unify[a_ == b_, c_ == d_] := unify[a - b, c - d];

unify[a_ <= b_, c_ <= d_] := unify[a - b, c - d];

unify[a_ < b_, c_ < d_] := unify[a - b, c - d];



(* Unification of arithmetical expressions. *)

unify[a_ + b_., a_ + c_.] := unify[b, c];

unify[a_ b_., a_ c_.] := unify[b, c];

unify[a_ + b_, c_ + d_] := 
        Block[{u}, substitution[u, unify[apply[u, b], apply[u, d]]] /; 
                !FalseQ[u = unify[a, c]]];

unify[a_ b_, c_ d_] := 
        Block[{u}, substitution[u, unify[apply[u, b], apply[u, d]]] /; 
                !FalseQ[u = unify[a, c]]];

unify[1/Var[n_], a_] := substitution[{Var[n] -> 1/a}] /; FreeQ[a, n];

unify[a_, 1/Var[n_]] := substitution[{Var[n] -> 1/a}] /; FreeQ[a, n];



(* Unification of compound expressions.*)

unify[f_[a___], f_[b___]] := unifylist[{a}, {b}];




(* Default case--arguments do not unify. *)

unify[_, _] := False;



(* Check if two lists of formulas unify. *)

unifylist[_, False] := False;

unifylist[False, _] := False;

unifylist[{}, {}] := substitution[];

unifylist[{}, {__}] := False;

unifylist[{__}, {}] := False;

unifylist[{a_}, {b_}] := unify[a, b];

unifylist[{a_, x___}, {b_, y___}] := 
	Block[{u},
		u = unify[a, b];
		substitution[u, 
                 	unifylist[apply[u, {x}], apply[u, {y}]]]
        ];
        
        


(* Rules for simplifying substitutions. *)

substitution[] = True;

substitution[___, False, ___] := False;

substitution[a___, True, b___] := substitution[a, b];

substitution[a___, substitution[b__], c___] := substitution[a, b, c];

substitution[{a__}, {b__}, c___] := substitution[Union[{a}, {b}], c];

substitution[{a___, b_, c___, b_, d___}, e___] :=
        substitution[{a, b, c, d}, e];



(* Apply a substitution to a formula. *)

apply[False, a_] := False;

apply[substitution[], a_] := a;

apply[substitution[s_], term_] := term //. s;


