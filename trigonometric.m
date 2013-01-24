(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* Copyright 1988 Wolfram Research Inc. *)

(* by Roman Maeder *)

(* all kinds of trigonometric simplifications *)

(* import Global`, as we anticipate these routines to be called
   frequently by mistake before reading the file *)

BeginPackage["Algebra`Trigonometry`", "UserInterface`"]

TrigDefs::usage = "TrigDefs[expr] tries to expand instances of Tan,
        Cot, Csc, and Sec."

TrigCanonical::usage = "TrigCanonical[expr] applies basic trigonometric
	simplifications to expr (e.g. Sin[-x] --> -Sin[x])."

TrigFactor::usage = "TrigFactor[expr] tries to write sums of trigonometric
	functions as products."

TrigReduce::usage = "TrigReduce[expr] writes trigonometric functions of
	multiple angles as sums of products of trigonometric functions of
	that angle."

TrigReduce::notes = "TrigReduce simplifies the arguments of trigonometric
	functions. It is in a way the inverse of TrigExpand"

TrigToComplex::usage = "TrigToComplex[expr] writes trigonometric functions
	in terms of complex exponentials."

ComplexToTrig::usage = "ComplexToTrig[expr] writes complex exponentials
	as trigonometric functions of a real angle."

TrigExpand::usage = "TrigExpand[expr] tries to write trigonometric
	functions of sums."

(* note: TrigExpand[] is built in *)

Begin["`Private`"]

`TrigDefsRel = {
    Tan[x_]  :> Sin[x]/Cos[x] /; simplify[Cos[x] != 0],
    Cot[x_]  :> Cos[x]/Sin[x] /; simplify[Sin[x] != 0],
    Csc[x_]  :> 1/Sin[x] /; simplify[Sin[x] != 0],
    Sec[x_]  :> 1/Cos[x] /; simplify[Cos[x] != 0]
  }

TrigDefsRel = Dispatch[TrigDefsRel]
Protect[TrigDefsRel]

TrigDefs[e_] := e //. TrigDefsRel


`TrigCanonicalRel = {
    Sin[(n_?Negative) x_ + y_] :> -Sin[-n x - y] /;
    	Order[x, y] == 1 && NumberQ[n],

    (* Cos is an even function *)
    Cos[(n_?Negative) x_ + y_] :>  Cos[-n x - y] /;
	Order[x, y] == 1 && NumberQ[n],


    (* Sin[x]^2 + Cos[x]^2 --> 1 etc.     a_. Sin[x_]^2 + a_. Cos[x_]^2 :> a,
    n_. Sin[x_]^2 + m_. Cos[x_]^2 :> m + (n-m)Sin[x]^2 /; IntegerQ[n-m],
    a_ + b_. Sin[x_]^2 :> a Cos[x]^2 /; a+b == 0,
    a_ + b_. Cos[x_]^2 :> a Sin[x]^2 /; a+b == 0,*)
    Cos[x_]^2 :> 1 - Sin[x]^2,


    Sin[r_Rational Pi]	:>   Sin[(r - 2 Floor[r/2]) Pi] /; r > 2,
    Cos[r_Rational Pi]	:>   Cos[(r - 2 Floor[r/2]) Pi] /; r > 2,
    Sin[r_Rational Pi]	:> - Sin[(r - 1) Pi] /; r > 1,
    Cos[r_Rational Pi]	:> - Cos[(r - 1) Pi] /; r > 1,
    Sin[r_Rational Pi]	:>   Sin[(1 - r) Pi] /; r > 1/2,
    Cos[r_Rational Pi]	:> - Cos[(1 - r) Pi] /; r > 1/2,
    Sin[r_Rational Pi]	:>   Cos[(1/2 - r) Pi] /; r > 1/4,
    Cos[r_Rational Pi]	:>   Sin[(1/2 - r) Pi] /; r > 1/4

}
TrigCanonicalRel = Dispatch[TrigCanonicalRel]
Protect[TrigCanonicalRel]

TrigCanonical[e_] := e //. TrigCanonicalRel

`TrigFactorRel = {
    a_. Sin[x_] + a_. Sin[y_] :> 2 a Sin[x/2+y/2] Cos[x/2-y/2],
    a_. Sin[x_] + b_. Sin[y_] :> 2 a Sin[x/2-y/2] Cos[x/2+y/2] /; a+b == 0,
    a_. Cos[x_] + a_. Cos[y_] :> 2 a Cos[x/2+y/2] Cos[x/2-y/2],
    a_. Cos[x_] + b_. Cos[y_] :> 2 a Sin[x/2+y/2] Sin[y/2-x/2] /; a+b == 0,

    a_. Sin[x_] Cos[y_] + a_. Sin[y_] Cos[x_] :> a Sin[x + y],
    a_. Sin[x_] Cos[y_] + b_. Sin[y_] Cos[x_] :> a Sin[x - y] /; a+b == 0,
    a_. Cos[x_] Cos[y_] + b_. Sin[x_] Sin[y_] :> a Cos[x + y] /; a+b == 0,
    a_. Cos[x_] Cos[y_] + a_. Sin[x_] Sin[y_] :> a Cos[x - y]

}
TrigFactorRel = Dispatch[TrigFactorRel]
Protect[TrigFactorRel]

TrigFactor[e_] := FixedPoint[(# /. TrigCanonicalRel /. TrigFactorRel)&, e]


`TrigExpandRel = {
    Sin[x_ + y_] :> Sin[x] Cos[y] + Sin[y] Cos[x],
    Cos[x_ + y_] :> Cos[x] Cos[y] - Sin[y] Sin[x],
    Sin[n_Integer x_] :> 
	If[n<0, -Sin[-n x], Sin[x] Cos[(n-1) x] + Cos[x] Sin[(n-1) x]],
    Cos[n_Integer x_] :> 
	If[n<0, Cos[-n x], Cos[x] Cos[(n-1) x] - Sin[x] Sin[(n-1) x]]
}

TrigExpandRel = Dispatch[TrigExpandRel]

Protect[TrigExpandRel]

TrigExpand[e_] := FixedPoint[(# /. TrigCanonicalRel /. TrigExpandRel)&, e]


`TrigReduceRel = {

    (* the following two formulae are chosen so as to allow easy
       reconstruction of TrigExpand[Sin[x]^n] or TrigExpand[Cos[x]^n].
       In these cases, Sin[n x] with even n does not occur.
       There we use another formula *)

    Cos[n_Integer x_] :> 2^(n-1) Cos[x]^n +
	Sum[ Binomial[n-j-1, j-1] (-1)^j n/j 2^(n-2j-1) Cos[x]^(n-2j),
	   {i, 1, n/2} ]		/; n > 0,

    Sin[m_Integer?OddQ x_] :>
    	Block[{p = -(m^2-1)/6, s = Sin[x]},
	      Do[s += p Sin[x]^k;
                 p *= -(m^2 - k^2)/(k+2)/(k+1),
                {k, 3, m, 2}];
	      m s]				/; m > 0,

    Sin[n_Integer?EvenQ x_] :> 
	Sum[ Binomial[n, j] (-1)^((j-1)/2) Sin[x]^j Cos[x]^(n-j),
	     {j, 1, n, 2} ]		/; n > 0,

    Sin[(c_.)(x_ + y_)] :> Sin[c x] Cos[c y] + Sin[c y] Cos[c x],
    Cos[(c_.)(x_ + y_)] :> Cos[c x] Cos[c y] - Sin[c x] Sin[c y],

    (* rational factors, "symb" does not have a value *)
    Sin[r_Rational x_] :> (Sin[Numerator[r] `symb] /. TrigReduceRel /.
    	`symb -> x/Denominator[r])		/; Numerator[r] != 1,
    Cos[r_Rational x_] :> (Cos[Numerator[r] `symb] /. TrigReduceRel /.
    	`symb -> x/Denominator[r])		/; Numerator[r] != 1,

    (* half angle args *)
    Cos[x_/2]^(n_Integer?EvenQ) :>
    			((1 + Cos[x])/2)^(n/2),
    Sin[x_/2]^(n_Integer?EvenQ) :>
    			((1 - Cos[x])/2)^(n/2),
    Sin[r_ (x_.)] Cos[r_ (x_.)]	:> Sin[2 r x]/2	/; IntegerQ[2r],


    (* Value at special points *)
    Cos[a_?integer Pi] :> (-1)^a,

    Sin[a_?integer Pi] :> 0

}
TrigReduceRel = Dispatch[TrigReduceRel]
Protect[TrigReduceRel]

TrigReduce[e_] := e //. TrigReduceRel;

`TrigToComplexRel = {

    Sin[x_] :> -I/2 (Exp[I x] - Exp[-I x]),
    Cos[x_] :>  1/2 (Exp[I x] + Exp[-I x])
}
TrigToComplexRel = Dispatch[TrigToComplexRel]
Protect[TrigToComplexRel]

TrigToComplex[e_] := e //. TrigCanonicalRel //. TrigToComplexRel


`ComplexToTrigRel = {

    Exp[c_Complex x_.] :> Exp[Re[c] x] (Cos[Im[c] x] + I Sin[Im[c] x])
}
ComplexToTrigRel = Dispatch[ComplexToTrigRel]
Protect[ComplexToTrigRel]

ComplexToTrig[e_] :=
	Cancel[e /. ComplexToTrigRel //. TrigCanonicalRel] //. TrigCanonicalRel


Protect[TrigDefs, TrigCanonical, TrigFactor, TrigReduce, TrigToComplex, ComplexToTrig]

End[]

EndPackage[]

TrigSimplify[e_] :=
	FixedPoint[(TrigReduce[TrigExpand[TrigFactor[#]]])&, TrigDefs[e]]



RewriteTrig[s_] := Block[{s0, s1}, (

	(* if the expression is free of trigonometric functions *)

	If[FreeQ[s, Sin] && FreeQ[s, Cos],
		Return[s]];

	(* rewrite trigonometric expressions *)

	s0 = EvaluateAssuming[not[s], TrigSimplify[s]];

	(* if changed during rewriting, simplify the sequent *)

	s1 = SimplifyIfChanged[s, s0];

	(* if the sequent changed, print it out *)

	If[s1 =!= s, 
		(print["rewrite trigonometric expressions"]; 
		PrintMessage[SimplifyMessage])];

	Return[s1])];

