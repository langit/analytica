(* Copyright 1988, 1989 Wolfram Research Inc., V1.2 *)

(* Gosper algorithm for indefinite summation *)

(* by Roman Maeder *)

GosperSum[an_, range_] := sum[an, range] /; !FreeQ[an, Var];

(* insert known special cases here *)
GosperSum[Binomial[n_, k_], {k_, 0, n_, 1}] := 2^n
GosperSum[Binomial[n_, k_], {k_, m_Integer, n_, 1}] :=
	2^n - Sum[Binomial[n, k], {k, 0, m-1}]

(* linearity *)
GosperSum[an_ + bn_, {var_, n0_, n1_, inc_}] :=
	GosperSum[an, {var, n0, n1, inc}] + GosperSum[bn, {var, n0, n1, inc}]

GosperSum[c_ an_, {var_, n0_, n1_, inc_}] :=
	c GosperSum[an, {var, n0, n1, inc}] /; FreeQ[c, var]

(* default increment *)
GosperSum[an_, {var_, n0_, n1_}] := GosperSum[an, {var, n0, n1, 1}]

(* default startvalue *)
GosperSum[an_, {var_, n1_}] := GosperSum[an, {var, 1, n1, 1}]

(* trivial cases *)
GosperSum[an_, {var_, n0_, n1_, 1}] := 
	an (n1 - n0 + 1)	/; FreeQ[an, var]

GosperSum[an_, {var_, n0_, n0_, _}] := an /. var -> n0

Subvar[expr_, old_, new_] := expr /. old -> new

PolyDegree[0, _] = -1;
PolyDegree[expr_, var_] := Exponent[expr, var];

GosperSum[an_, {var_, n0_, n1_, 1}] :=
    Block[{pn, qn, rn, an1, rnj, jj, res, resn, resp, rat, ann, qrpos, ii,
	   qrneg, dqrpos, dqrneg, dk, dp, fn, sn, k0, eq, i, s0, s1},
	ann = an;
	an1 = Subvar[ann, var, var-1];
	rat = ann/an1; (* user-defined rules take effect here *)
	rat = Together[rat];
	qn = Expand[ Numerator[rat] ];
	rn = Expand[ Denominator[rat] ];
	If[!PolynomialQ[qn, var] || !PolynomialQ[rn, var],
		(* not a rational function *)
		Return[Sum[an, {var, n0, n1, 1}]]];
	pn = 1;
	rnj = Expand[Subvar[rn, var, var+jj]];
	res = Resultant[qn, rnj, var];
	res = FactorList[res];
	res = Map[#[[1]]&, res];
	(* find factors linear in jj *)
	resp = Cases[res, jj+_Integer]; 
	resn = Cases[res, -jj+n_Integer];
	res = Join[-(resp - jj), resn + jj];
	res = Select[res, Positive];
	(* adjust for positive integer zeros *)
	Do[  Block[{gn, gnj, resi = res[[ii]], i},
		gn = PolynomialGCD[qn, Expand[Subvar[rn, var, var+resi]], var];
		qn = Cancel[qn/gn];
		gnj = gn;
		Do[	pn = Expand[pn gnj];
			gnj = Expand[Subvar[gn, var, var-i]],
		   {i, resi}];
		rn = Cancel[rn/gnj]
	     ],
	   {ii, Length[res]} ];
	(* find degree bound *)
	qn = Expand[Subvar[qn, var, var+1]];
	dp = PolyDegree[pn, var];
	qrpos = Expand[qn+rn]; dqrpos = PolyDegree[qrpos, var];
	qrneg = Expand[qn-rn]; dqrneg = PolyDegree[qrneg, var];
	If[ dqrpos <= dqrneg,
		dk = dp - dqrneg,
	(* else *)
		If[ dqrneg < dqrpos - 1 || dqrneg == -1,
		    dk = dp - dqrpos + 1,
		(* else *)
		    k0 = - Cancel[Coefficient[qrneg, var, dqrneg]/
			Coefficient[qrpos, var, dqrpos]];
		    dk = If[IntegerQ[k0], Max[k0, dp - dqrpos + 1],
		    		dp - dqrpos + 1]
		]
	];
	If[ dk >= 0, (* solution possible *)
		fn = Sum[f[ii] var^ii, {ii, 0, dk}];
		eq = Expand[pn - qn fn + rn Subvar[fn, var, var-1]];
		eq = CoefficientList[eq, var];
		eq = Solve[Thread[eq == 0], Array[f, dk+1, 0]];
		If[Length[eq] > 0,
		    fn = fn /. eq[[1]];
		    fn = fn /. f[0] -> 0; (* summation constant *)
		    sn = Cancel[qn/pn fn] ann;
		    (* crude test for infinity *)
		    s1 = sn /. var -> n1;
		    s0 = (sn /. var -> n0) - (ann /. var -> n0);
		    Return[s1 - s0],
		(* else fail *)
		    Return[Sum[an, {var, n0, n1, 1}]]
		],
	(* else fail *)
		Return[Sum[an, {var, n0, n1, 1}]]
	]
    ]

Protect[GosperSum]
