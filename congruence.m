(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* All variables are integers. I want to avoid having to include this
 assumption as a condition for each rule. Can I use packages for this
 purpose?  *)

(* I also need to specify "relatively_prime" and "gcd". I will use
 the versions of these provided by Mathematica for the short run *)

BeginPackage["congruences`", "UserInterface`", "SystemInterface`"]

RewriteCongruences::usage =
	" RewriteCongruences[s] rewrite the congruence expression in 's'. ";

Begin["Private`"]

(* Rules for congruences. Eventually, I want to include rules for solving \
   equations involving congruences also. *) 

CongruenceRules = {

	congruent[a_?NumberQ, b_?NumberQ, c_?NumberQ] :=
		IntegerQ[(a - b)/c];

	congruent[k_ a_, k_ b_,  k_ m_] := 
		congruent[a, b, m];

	congruent[k_ a_, k_ b_, m_] := 
		True /; congruent[a, b, m];

	congruent[a_ + c_, b_ + d_, m_] := 
		True /; congruent[a, b, m] && congruent[c, d, m];

	congruent[a_ c_, b_ d_, m_] := 
		True /; congruent[a, b, m] && congruent[c, d, m];

	congruent[a_^n_, b_^n_, m_] := 
		True /; 
		integer[n] &&  congruent[a, b, m] && WeakSimplify[n>=0];

	congruent[a_, b_, m_ n_] := 
		and[congruent[a, b, m], congruent[a, b, n]] /; 
		gcd[m, n] == 1;

	congruent[a_, b_, m_ n_] := 
		True /; congruent[a, b, m];

	congruent[a_ d_, b_ d_, m_] := 
		congruent[a, b, m] /; gcd[d, m] == 1;

	congruent[a_ d_, b_ d_, m_] := 
		congruent[a, b, m / gcd[d,m]];

	congruent[p_, q_, m_] := 
		WeakSimplify[integer[(p-q)/m]] /; 
		TruthQ[WeakSimplify[integer[(p-q)/m]]]
	
	};

TruthQ[a_] := TrueQ[a] || FalseQ[a];

CongruenceRules = Dispatch[CongruenceRules]

RewriteCongruences[e_] := e /. CongruenceRules;


End[]

EndPackage[]

