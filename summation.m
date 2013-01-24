(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* RULES FOR SUMMATION. *)

SimplifySummation[1][f_] := 
	If[!FreeQ[f, sum] && simpler[f, GosperSimplify[f]],
		GosperSimplify[f],
		f];


SimplifySummation[2][f_] :=
	If[!FreeQ[f, sum] && simpler[f, f //. SumRewriteRules],
		f //. SumRewriteRules,
		f];

SimplifySummation[3][f_] :=
	If[!FreeQ[f, sum], f /. SumSimplifyRules, f];


simpler[a_, b_] := 
	NumberOfAppearances[a, _sum] > NumberOfAppearances[b, _sum];




(* Global rules for summation. *)



(* A summation with each term constant. *)

sum[n_?NumberQ, {v_, min_, max_}] := n (max-min+1);




(* Standard Form for range of Summation. *)

sum[a_, {v_, n1_, n2_}] := 
	If[n2 - n1 >= 0, 
		Sum[a, {v, n1, n2}], 
		- Sum[a, {v, n2 + 1, n1 - 1}]] /;
	IntegerQ[n2 - n1];



(* Factor a constant term from a summation. *)

sum[a_ f_, {v_, n__}] := a sum[f, {v, n}] /; FreeQ[a, v] && FreeQ[a, Var];



(* sum[a^(c k+n) b, {k, n1, n2}] == a^n sum[a^(c k) b, {k, n1, n2}] *)

sum[a_^(c_ + n0_) b_, {v_, range__}] :=
	a^n0 sum[a^c b, {v, range}] /; FreeQ[a^n0, v] && FreeQ[a^n0, Var];



(* sum[f[k], {k, n1, n2, condition[k]}] is a summation with restriction,
   i.e. a  summation in which all terms must satisfy some condition. *)

sum[f_, {v_, n1_Integer, n2_Integer, cond_}] :=
	Sum[If[cond, f, 0], {v, n1, n2}];

sum[f_, {v_, n1_, n2_, True}] := sum[f, {v, n1, n2}];

sum[f_, {v_, n1_, n2_, False}] := 0;



(* Some properities of binomial coefficients. *)

Unprotect[Binomial];

Binomial/: (0 <= Binomial[a_, b_]) := True;

Binomial/: (0 < Binomial[a_, b_]) := not[Binomial[a, b] == 0];

Binomial/: (Binomial[a_, b_] <= 0) := (Binomial[a, b] == 0);

Binomial/: (Binomial[a_, b_] < 0) := False;

Binomial/: (Binomial[a_, b_] == 0) := or[b < 0, 0 < b-a];

Protect[Binomial];



(* Collect summations with the same range. *)



(* Rules for collecting summations. *)

SumSimplifyRules := {



(* Split off additional terms of summation. *)

sum[a_, {v_, n1_, n2_ + n_Integer?Positive}] :>
        sum[a, {v, n1, n2}] + Sum[a, {v, n2 + 1, n2 + n}],



(* Merge summations with the same range. *)

n1_. sum[a_, range_] + n2_ sum[b_, range_] :> sum[(n1 a + n2 b), range],



(* sum[f, {k, n1, n2, cond}] + sum[f, {k, n1, n2, not[cond]}] ==
   sum[f, {k, n1, n2}] *)

a_. sum[f_, {v_, min_, max_}] + b_. sum[f_, {v_, min_, max_, cond_}] :>
	a sum[f, {v, min, max, not[cond]}] /; (a+b === 0),



(* sum[f, {k, n1, n2, cond1}] + sum[f, {k, n1, n2, cond2}] ==
   sum[f, {k, n1, n2, or[cond1, cond2]}] when and[cond1, cond2] = False *)

a_. sum[f_, {v_, min_, max_, cond1_}] + 
a_. sum[f_, {v_, min_, max_, cond2_}] :>
	a sum[f, {v, min, max, WeakSimplify[or[cond1, cond2]]}] /; 
	(!WeakSimplify[and[cond1, cond2]]),



(* Append two summations. *)

a_. sum[f_, {v_, n1_, n2_}] + a_. sum[f_, {v_, n3_, n4_}] :>
	a sum[f, {v, n1, n4}] + a sum[f, {v, n3, n2}] /; 
	IntegerQ[n3 - n2] || IntegerQ[n4 - n1],



(* Subtract the first or last part from a summation. *)

a_. sum[f1_, {v_, n1_, n2_}] + b_. sum[f2_, {v_, n3_, n4_}] :>
	a sum[f1, {v, n1, n3-1}] - a sum[f1, {v, n2+1, n4}] /; 
	(IntegerQ[n4 - n2] || IntegerQ[n3 - n1]) && WeakSimplify[a f1 + b f2 == 0],



(* Change the range when the lower bound exceeds the upper bound. *)

sum[f_, {v_, min_, max_, c___}] :>
	-sum[f, {v, max+1, min-1, c}] /; WeakSimplify[min > max],



(* Two sufficient rules for deciding the sign of a summation. *)

sum[f_, range_] < 0 :> False /; WeakSimplify[f >= 0],

sum[f_, range_] <= 0 :> False /; WeakSimplify[f >= 0]


};


printandreturn[a_]:=
(Print["Result  ", a]; a);

(* put the summation SumWrite and rewrite by changing range and index *)

SumRewriteRules = {



(* Geometric summations, sum[a^k, {k, n, m}] == (a^(m+1) - a^n) / (a - 1) *)

sum[a_, {v_, min_, max_}] :> Block[{temp}, 
	(temp^(max + 1) - temp^min)/(temp - 1) /; 
	FreeQ[temp = a^(1/v), v]],



(* k Binomial[m, k] == m Binomial[m-1, k-1] *)

k_^Optional[n_Integer] Binomial[m_, k_] :>
	k^(n-1) m Binomial[m-1, k-1] /; Positive[n],



(* sum[a + b, {k, n1, n2}] == sum[a, {k, n1, n2}] + sum[b, {k, n1, n2}] *)

sum[Plus[a_, b__] c_., range_] :> Map[sum[# c, range]&, Plus[a, b]],

sum[(a_ + b_)^n_Integer?Positive c_., range_] :> 
	Map[sum[# c, range]&, Expand[(a+b)^n]],



(* Sum of binomial series. *)

sum[a_. Binomial[n1_, k_], {k_, m_Integer, n2_}] :>

	(* the binomial *)

	(Together[1 + a^(1/k)])^n1 +

	(* the remainder of the summation *)

	sum[a Binomial[n1, k], {k, n1+1, n2}] - 

	(* the missing term for 0<=k<m *)

	sum[a Binomial[n1, k], {k, 0, m-1}] /; 

	FreeQ[a^(1/k), k] && IntegerQ[n2-n1],



(* sum[f[k+1], {k, n1, n2}] == sum[f[k], {k, n1+1, n2+1}] *)

sum[t_, {v_, min_, max_}] :> 

	sum[t /.(v -> v-1), {v, min+1, max+1}] /;

	!FreeQ[t, v + n_Integer?Positive] && SimplerWhenDecrease[t, v],



(* sum[f[k-1], {k, n1, n2}] == sum[f[k], {k, n1-1, n2-1}] *)

sum[t_, {v_, min_, max_}] :> 

	sum[t /.(v -> v+1), {v, min-1, max-1}] /;

	!FreeQ[t, v + n_Integer?Negative] && SimplerWhenIncrease[t, v],



(* Split summation. *)

sum[a_, {v_, n1_, n2_ + n_Integer}] :>
        sum[a, {v, n1, n2}] + sum[a, {v, n2 + 1, n2 + n}]

};



(* Decide if a term will be more complicated if "v" is replaced by 
with "v-1". *)

SimplerWhenDecrease[a_+b_, v_] := 
	SimplerWhenDecrease[a, v] && SimplerWhenDecrease[b,v];

SimplerWhenDecrease[a_ b_, v_] := 
	SimplerWhenDecrease[a, v] && SimplerWhenDecrease[b,v];

SimplerWhenDecrease[Power[a_, b_. c_], v_] := FreeQ[a, v] && FreeQ[b, v];

SimplerWhenDecrease[f_[v_], v_] := False;

SimplerWhenDecrease[v_, v_] := True;

SimplerWhenDecrease[sum[t_, {v1_, min_, max_}], v_] := 
	SimplerWhenDecrease[t, v] && SimplerWhenDecrease[min, v] &&
	SimplerWhenDecrease[max, v];

SimplerWhenDecrease[c_, v_] := 
	FreeQ[c, v] || FreeQ[c/.(v->v-1), v+n_Integer?Negative];



(* Decide if a term will be more complicated if "v" is 
replaced by "v+1". *)

SimplerWhenIncrease[a_+b_, v_] := 
	SimplerWhenIncrease[a, v] && SimplerWhenIncrease[b,v];

SimplerWhenIncrease[a_ b_, v_] := 
	SimplerWhenIncrease[a, v] && SimplerWhenIncrease[b,v];

SimplerWhenIncrease[Power[a_, b_. c_], v_] := FreeQ[a, v] && FreeQ[b, v];

SimplerWhenIncrease[f_[v_], v_] := False;

SimplerWhenIncrease[v_, v_] := True;

SimplerWhenIncrease[sum[t_, {v1_, min_, max_}], v_] := 
	SimplerWhenIncrease[t, v] && SimplerWhenIncrease[min, v] && 
	SimplerWhenIncrease[max, v];

SimplerWhenIncrease[c_, v_] := 
	FreeQ[c, v] || FreeQ[c/.(v->v+1), v+n_Integer?Positive];



sum1[f_, {v_, n1_, n2_, _}] := sum[f, {v, n1, n2}];


RewriteSum[s_] := Block[{s0, s1}, (

	(* Rewrite summation expressions. *)

	s0 = EvaluateAssuming[not[s], s //. SumRewriteRules]; 

 	s0 = GosperSimplify[s0]; 

	(* If changed during rewriting, simplify the sequent. *)

	s1 = SimplifyIfChanged[s, s0];

	(* If the sequent changed, print it out. *)

	If[s1 =!= s, 
		(print["rewrite summation expressions"]; 
		PrintMessage[SimplifyMessage])];

	Return[s1])];



GosperSimplify[s_] :=
	 (s /. sum -> GosperSum1) /. Sum -> sum1; 

GosperSum1[an_, {k_, min_, max_, cond_}] := sum[an, {k, min, max, cond}];

GosperSum1[an_, range_] := 
	If[FreeQ[an, Var], GosperSum[an, range], sum[an, range]];





