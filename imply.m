(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* PROVING *)


(* instantiation for current sequent and current instantiation *)

curinstantiation = True;

TheoremsProved = {};

ProveHistory = {};


(* ProveByInduction tries to prove f by first kind induction on n,
   i.e. tries to prove f[0] /\ (f[n-1] -> f[n]) *)

SetAttributes[ProveByInduction , {HoldRest}];

ProveByInduction[{n_, n0_, nbases_}, f_] := Block[{temp, tempk}, (

	StartProof;

	ProveHistory = {};

	StartSection[Temp];

	(* initialize the theorem label *)

	label = "1";

	PrintBold["Theorem :"];

	PrintSequent[HoldForm[f]];

	AppendTo[TheoremsProved, Printform[HoldForm[f]]];

	PrintBold["Proof :"];

	print["prove by induction on ", ToString[n], "\n"];

	integer[n] = True;

	temp = Skolemize[f, NegativePosition, {}];
	
	(* try the induction bases, with n = n0, ..., n0 + nbases - 1 *)

	For[tempk = 0, tempk < nbases, tempk++, 
	
	print["base case with ", ToString[n], " = ", ToString[n0 + tempk]];

	(* if one of the bases fails, return with fail *)

	If[FalseQ[Verify[seq[True, Skolemize[f /. n -> n0 + tempk, NegativePosition, {}]]]], 

		PrintResult["RESULT", Fail];
		sequent = False;
		EndSection[];
		EndProof;
		Return[]];
	];

	(* the induction steps *)
	
	print["induction step"];
	Given[n >= n0];

	Verify[seq[Apply[and, Map[Skolemize[f /. n -> n + # - 1, PositivePosition, {}]&, Range[nbases]]], 
			Skolemize[f /. n -> n+nbases, NegativePosition, {}]]];

	EndSection[];

	EndProof;)];


ProveByInduction[{n_, n0_}, f_] := ProveByInduction[{n, n0, 1}, f];

ProveByInduction[n_, f_] := ProveByInduction[{n, 0}, f];



(* try to prove a formula with quantifiers *)

SetAttributes[Prove, {HoldFirst}];

Prove[f_] :=  (

	StartProof;

	ProveHistory = {};

	StartSection[Temp];

	PrintBold["Theorem :"];

	PrintSequent[HoldForm[f]];

	AppendTo[TheoremsProved, Printform[HoldForm[f]]];

	PrintBold["Proof :"];

	(* sequent is the formula to be proved *)

	sequent = seq[True, Skolemize[f, NegativePosition, {}]];

	(* initialize the theorem label *)

	label = "1";

	(* prove the theorem and print the result *)

	Verify[sequent];

	EndSection[];

	EndProof;);


(* prove if changed *)

VerifyIfNotSame[s0_, s_] :=
	If[s =!= s0, Verify[s], False];


(* prove *)

Verify[s_] := Block[{sequent}, (

	(* simplify *)

	sequent = StrongSimplify[s]; PrintMessage[SimplifyMessage];

	If[DepthCount > 0, 
		Return[TryProving[sequent]]];

	orelse[

	(* try proving *)

	TryProving[sequent],

	(* rewrite and prove *)

	RewriteAndProve[sequent],

	(* open the definitions of functions as the last technique *)

	VerifyIfNotSame[sequent, OpenDefinition[sequent]],

	(* If none of the above techniques works, Fail after all *)

	PrintResult["after all", Fail];

	False])];



(* rewriting and proving the given formula *)

RewriteAndProve[s_] := orelse[

	(* the followings are all used to rewrite the sequent *)

	(* try to substitute using equations appearing in hypothesis *)

	TryProveIfNotSame[sequent, 
		sequent = SubstEquation[sequent]],

	(* apply user given rewrite rules *)

	TryProveIfNotSame[sequent, 
		sequent = Rewriting[sequent]],

	(* try induction *)

	TryInduction[sequent],

	(* try to rewrite summation expressions *)

	TryProveIfNotSame[sequent, 
		sequent = RewriteSum[sequent]],

	(* try to rewrite trigonometric expressions *)

	TryProveIfNotSame[sequent, 
		sequent = RewriteTrig[sequent]],

	(* factor the expression in equations and inequalities *)

	TryProveIfNotSame[sequent, 
		sequent = Factorize[sequent]],

	(* solve linear equalities *)

	TryProveIfNotSame[sequent, 
		sequent = SolveEquation[sequent]],

	(* if changed during the above, try again, otherwise fail *)

	If[s =!= sequent, RewriteAndProve[sequent], False]] ;


(* if the first sequant is difference from the second, try proving the 
   second *)

TryProveIfNotSame[s0_, s_] := 
	If[s =!= s0, TryProving[s], False];


TryProving[s_] := Block[{temp, temph},

	(* print the formula to be proved *)

	PrintSequent[s];

	SucceedWith[

	If[TrueQ[s], 

		(* the case when the sequent is simply True *)

		TryOtherBranches[True],

		(* otherwise *)

		orelse[ Imply[s], ProveUsingBound[s]]]]];


(* Start of Imply *)


(* equation *)
(* check if there is a equation in the conclusion which is satisfiable *)

Imply[seq[h_, a_  ==  b_]] :=  Block[{u,u1, temph},
	u1 /;
	(!FalseQ[u = unify[a, b]] && !FalseQ[u1 = SucceedWith[
	  PrintResult["equation", u]; 
	  TryOtherBranches[u]]])];

Imply[seq[h_, or[c1___, a_  ==  b_,  c2___]]] :=  Block[{u,u1, temph},
	u1 /;
	(!FalseQ[u = unify[a, b]] && !FalseQ[u1 = SucceedWith[
	  PrintResult["equation", u]; 
	  TryOtherBranches[u]]])];


(* inequality *)
(* check if there is a inequality in the conclusion which is satisfiable *)

Imply[seq[h_, a_  <=  b_]] :=  Block[{u,u1, temph},
	u1 /;
	(!FalseQ[u = unify[a, b]] && !FalseQ[u1 = SucceedWith[
	  PrintResult["inequality", u]; 
	  TryOtherBranches[u]]])];

Imply[seq[h_, or[c1___, a_  <=  b_,  c2___]]] := Block[{u,u1, temph},
	u1 /;
	(!FalseQ[u = unify[a, b]] && !FalseQ[u1 = SucceedWith[
	  PrintResult["inequality", u]; 
	  TryOtherBranches[u]]])];

Imply[seq[Var[x_] == f_, c_]] := Block[{u,u1, temph},
	u1 /;
	(FreeQ[f, x] && !FalseQ[u1 = SucceedWith[
	 PrintResult["add restriction:", x != f]; 
	 Restriction = and[Restriction, not[Var[x] == f]]; 
	 Given[not[Var[x] == f]];
	 TryOtherBranches[True]]])];

Imply[seq[and[h1___, Var[x_] == f_, h2___], c_]] := Block[{u,u1, temph},
	u1 /;
	(FreeQ[f, x] && !FalseQ[u1 = SucceedWith[
	 PrintResult["add restriction:", x != f]; 
	 Restriction = and[Restriction, not[Var[x] == f]]; 
	 Given[not[Var[x] == f]];
	 TryOtherBranches[True]]])];



(* Match *)
(* check if a disjunct of the conclusion matches a conjunct of the 
   hypothesis *)

Imply[seq[h_, c_]] := u /;(!FalseQ[SucceedWith[u  =  disjunct[h, c]]]); 


(* prove by "and split" *)
(* " H -> (A /\ B) " is equivalent to " (H -> A) /\ ((H /\ A) -> B) " *)

(* to prove " H -> (A /\ B) " *)

Imply[seq[h_, and[a_, b__]]] := (

	print["and split \n"];

	(* try " H -> A "  first and then try " (H /\ A) -> B " *)

	SequentialTry[ seq[h, a],   seq[and[h, simple[a]], and[b]]]);

(* to prove " H -> (A /\ B) \/ C " *)

Imply[seq[h_, or[c1___, and[a_, b__], c2___]]] := (

	print["and split\n"];

	(* try " H -> (A \/ C) " first and then "(H /\ A) -> (B \/ C) " *)

	SequentialTry[ seq[h,  or[c1, a, c2]],
		seq[and[h, simple[a]],  or[c1, and[b], c2]]]);


(* prove by "cases" *)
(* " (A \/ B) -> C " is equivalent to " (A -> C) /\ (B -> C \/ A) " *)

(* to prove " (A \/ B) -> C " *)

Imply[seq[or[a_, b__], c_]] := (

	print["cases\n"];

	(* try " A -> C " first and then " B -> (C \/ A) " *)

	SequentialTry[ seq[a, c],   seq[or[b], or[c, simple[a]]]]);

(* to prove " ( H /\ ( A \/ B )) -> C " *)

Imply[seq[and[h1___, or[a_, b__], h2___], c_]] := (

	print["cases\n"];

	(* try " (H /\ A) -> C " first and then " (H /\ B) -> (C \/ A) " *)

	SequentialTry[ seq[and[h1, a, h2],  c],

		seq[and[h1, or[b], h2],  or[c, simple[a]]]]);


simple[_or] = simple[_and] = simple[_imp] = NIL;

simple[a_] := a;


(* Back-chain *)

Imply[seq[h0_, or[c0___, c_, c1___]]] := Block[{u}, u /; 
	!FalseQ[u = Backchain[seq[h0, or[c0, c1]], Lemmas[Head[c]], c]]];

Imply[seq[h0_, c_]] := Block[{u}, u /; 
	!FalseQ[u = Backchain[seq[h0, False], Lemmas[Head[c]], c]]];


(* otherwise fail *)

Imply[s_] := False;


(* end of Imply *)



(* check if false *)

FalseQ[x_] := (x === False);



(* "orelse" checks if either one of the two formulas is not false. *)

SetAttributes[orelse, HoldRest];

orelse[f_] := f;

orelse[False, f2__] := orelse[f2];

orelse[f1_, f2__] := f1;



(* prove with back chaining, the first argument of Backchain is the current
   sequent, the second is a conjunction of lammes and the third is the
   conclusion part want to be matched with one of the lemmas *)


(* try each lemma sequentially *)

Backchain[s_, and[a_,rest__], c_] :=
	orelse[ Backchain[s, a, c],
		Backchain[s, and[rest], c] ];


(* when "c" matches the conclusion part of a lemma, back chain *)

Backchain[s_, imp[b_, c1_], c_] :=   Block[{u1},

	MatchingState = lemmma;

	CurrentLemma = imp[b, c1];

	BranchStackPush[{or[b, s], 0}];

	(* if the backchaining rule can be applied here *)

	If[FalseQ[u1 = conjunct[c1, c]], BranchStackPop[]];

	u1];



(* If backchaining can not be used *)

Backchain[___] :=  False; 



(* verify and show theorem label *)

TryPart[f_, l_] :=  
	If[label===0, 
	(label = templ; print["back chaining"]; Verify[f]),
	(SetAndPrintLabel[StringJoin[label, ".", l]]; Verify[f])]; 



(* "SequentialTry[p1, p2]" attempts to prove p1 first and then p2,
   the instantiation obtained from proving p1 should be applied to p2 *)

SequentialTry[p1_, p2_] := Block[{u1},

	BranchStackPush[{p2, label}];

	(* try the first part *)

	If[FalseQ[u1 = TryPart[p1, "1"]], BranchStackPop[]];

	u1];

TryOtherBranches[u_] := Block[{
	u1, tempseq, 
	templ = label, 
	curinstantiation = substitution[curinstantiation, u],
	tempstack = BranchStack},

	If[BranchStackEmpty[], 
		If[FalseQ[u1 = TryRestrict[curinstantiation]], 
			print["back tracking"]; SetAndPrintLabel[templ]; 
			PrintSequent[sequent];
			BranchStack = tempstack; Return[False],
		Return[u1]]];

	tempseq = BranchStackPop[];
	label = tempseq[[2]];
	tempseq = tempseq[[1]];

	If[FalseQ[u1 = TryPart[apply[curinstantiation, tempseq], "2"]], 
		print["back tracking"]; SetAndPrintLabel[templ]; 
		PrintSequent[sequent]; 
		BranchStack = tempstack; Return[False]];

	(* then the second part *)

	TryOtherBranches[u1]];



(* initialize the proof branch stack *)

BranchStack = {};


(* operations on the proof branch stack *)

BranchStackEmpty[] := (BranchStack === {});

BranchStackPush[a_] := (BranchStack = Prepend[BranchStack, a]);

BranchStackPop[] := Block[{temp}, temp = BranchStack[[1]] ; 
				  BranchStack = Drop[BranchStack, 1];
				  temp];


(* TryRestrict[u] tries to see if the instantiation "u" satisfies the 
   restrictions on variables *)

TryRestrict[u_] := Block[{temp=Restriction, temp0}, Restriction=True;

	If[temp === True, Return[u]];
	print["check restrict on instantiation"];

	(* if failed in proving that the restrictions hold, recover the 
	   Restriction and return with false *)

	If[FalseQ[temp0 = Verify[seq[True, apply[u, temp]]]], 
		Restriction = temp; Return[False]];

	(* otherwise return the result *)

	substitution[u, temp0]];


(* initialize the restrict on variable instantiations *)

Restriction = True;
