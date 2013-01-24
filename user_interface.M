(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* Functions provided to the user of Analytica. *)

BeginPackage["UserInterface`"]

(* these functions are provided in package simplify.M *)

seq::usage = 
	" seq[a, b] is the notation for a sequent, with hypothesis 'a' \
	and conclusion 'b'. ";

or::usage = 
	" or[a, b, ..., c] is the disjunction of a, b, ..., c. ";

and::usage = 
	" and[a, b, ..., c] is the conjunction of a, b, ..., c. ";

imp::usage = 
	" imp[a, b] means \" a -> b \". ";

not::usage = 
	" not[a] is the negation of 'a'. ";

eqv::usage = 
	" eqv[a, b] means 'a' and 'b' are equivalent. ";

if::usage = 
	" if[test, a, b] is a conditional expression. Its value is \
	'a' if 'test' is true and 'b' if 'test' is false. ";


WeakSimplify::usage = 
	" WeakSimplify[f] simplifies 'f' using the knowledge provided in the \
	current context. ";

StrongSimplify::usage =
	" StrongSimplify[f] simplifies 'f' in a more powerful way than \
	simplify, it also costs more time. ";


(* these functions are provided in package functions.M *)

Continuous::usage = 
	" Continuous[f[x], {x, x0}] specifies that 'f' is continuous \
	at point 'x0'. ";

round::usage = 
	" round[a] gives the nearest integer to 'a'. Thus, \
	round[n + 1/2] is n+1. ";

ContinuousFunction::usage = 
	" ContinuousFunction[f] holds provided 'f' is continuous \
	everywhere on its domian. ";

UniformlyContinuous::usage =
	" UniformlyContinuous[f] holds when 'f' continues uniformly on \
	its range. ";

UniformlyConvergent::usage =
	" UniformlyConvergent[f[x], {x, c1, c2}] means 'f' converges \
	uniformly on interval [c1, c2]. ";


IsConstant::usage = 
	" IsConstant[f, x] will be true if 'f' is an expression \
	that is independent of 'x'. ";

Increasing::usage = 
	" Increasing[f] indicates that 'f' is a monotonically increasing \
	function. ";

Decreasing::usage = 
	" Decreasing[f] indicates that 'f' is a monotonically decreasing \
	function. ";

Bounded::usage = 
	" Bounded[f] indicates 'f' is a bounded function on its domain. ";

Closed::usage = 
	" Closed[s] specifies that 's' is a closed set. ";

ClosedInterval::usage = 
	" ClosedInterval[a, b] is the interval [a, b]. ";

inverse::usage = 
	" inverse[f] is the inverse of the function 'f'. (Provided the \
	inverse exists). ";


delta::usage = 
	" delta[f][epsilon] is the delta in an epsilon - delta argument \
	about the continuity of a real function 'f'. ";

Bound::usage = 
	" Bound[f] is an upper bound on the absolute value of 'f' on its \
	domain. ";

Domain::usage =
	" Domain[f] specifies the domain set of function 'f'. ";


sum::usage = 
	" sum[f, {k, n1, n2}] is the symbol for summation. The index 'k' \
	goes from 'n1' to 'n2'.  sum[f, {k, n1, n2, cond}] is for \
	conditional summation where only terms that satisfy 'cond' are \
	included. ";

product::usage = 
	" product[f, {k, n1, n2}] is the symbol for product. The index \
	'k' goes from 'n1' to 'n2'. ";

limit::usage = 
	" limit[f[x], {x, l}] gives the limit value of 'f' as 'x' \
	tends to 'l'. ";

infinity::usage = 
	" infinity denotes the positive infinity. ";

Convergent::usage = 
	" Convergent[f] means that the limit expression 'f' converges to \
	a finite value. ";

(* these functions are provided in package environment.M *)

Facts::usage = 
	" Facts[f] lists the lemmas having the head 'f' which have no \
	hypotheses. ";
    

Lemmas::usage = 
	" Lemmas[f] lists the lemmas having the head 'f' that do have \
	hypotheses. ";
    

AddLemma::usage = 
	" AddLemma[L] adds 'L' as a lemma that may be used when \
	proving some formula that matches its conclusion part, universal \
	quantification can appear in lemmas. ";

AddRule::usage = 
	" AddRule[r] adds 'r' as a rewrite rule, 'r' can be either \
	conditional or unconditional. Conditional rewrite rules have the \
	form \" imp[condition, left == right] \". Unconditional rules: \
	\" left == right \". Universal quantification can be used in \
	rules.";

AddDefinition::usage = 
	" AddDefinition[f[a,...,c]==body] adds the definition of function \
	'f'. The definition will not be opened until all other proof \
	techniques have failed. Then all will be opened simultaneously. ";


UserRules::usage = 
	" UserRules is the set of local rewrite rules provided by the \
	user. ";

CurrentPath::usage = 
	" CurrentPath is a list of the sections that contain the current \
	context section as a subsection. "


CurrentSection::usage = 
	" CurrentSection is the current context section. ";

StartSection::usage = 
	" StartSection[a] begins a proof context with name 'a'. The \
	knowledge introduced to this context is only accessable from \
	within the context. ";

EndSection::usage = 
	" EndSection[] closes the current proof context. ";


Given::usage = 
	"Given[z] introduces the property 'z' into the current \
	proof section. (See also GivenTo, StartSection).";

GivenTo::usage = 
	"GivenTo[z, s] introduces the property 'z' into the proof \
	section 's'. (See also Given, StartSection).";

Initialize::usage = 
	" Initialize[] clears the knowledge base of the \
        current proof context. ";

ProveAndSave::usage = 
	" ProveAndSave[f] tries to prove formula 'f' and then introduces \
	  'f' into the current proof context. (See also Prove, Given).";

ProveAndSaveTo::usage = 
	" ProveAndSaveTo[f, s] tries to prove formula 'f' and then \
	introduces 'f' into the proof context 's'. (See also Prove, \
	GivenTo).";

(* these functions are provided in package prover.M *)

SetPrint::usage =
	" SetPrint sets the flags for both SuccessStepsOnly and TeXOn. ";

TeXOn::usage = 
	" TeXOn is the flag for the format of output. The output will be \
	in TeX form if the flag is True, otherwise the output is in \
	normal Mathematica form. ";

SuccessStepsOnly::usage =
	" SuccessStepsOnly is the flag used to decide if only success \
	steps are printed out. ";

EndDocument::usage =
	" EndDocument is used to put the ending to the TeX file. "

Abbreviate::usage = 
	"Abbreviate[f1, f2] takes 'f2' as an abbreviation for 'f1'. ";
	
PrintAbbreviation::usage = 
	"PrintAbbreviation[] print the abbreviation information. ";

PrintGiven::usage = 
	"PrintGiven[] prints out the given properties. ";

PrintDefinition::usage = 
	"PrintDefinition[] prints the definitions introduced by user. ";

Newpage::usage =
	"Newpage[] sets a page break when the output mode is TeX. ";

Prove::usage = 
	" Prove[f] attempts to prove the formula 'f'. ";


ProveByInduction::usage = 
	" ProveByInduction[{n, n0, nbases}, f] tries to \
	prove 'f' by induction on 'n', with 'nbases' base cases : \
	n = n0, n = n0 + 1, ..., n = n0 + nbases - 1. \
	In other words, it tries to prove \
	(f[n0]  & f[n0 + 1] & ... & f[n0 + nbases - 1]) & \
	((f[n] & f[n+1] & ... & f[n + nbases - 1]) -> f[n + nbases]). \
	The default value for 'nbases' is 1, \
	ProveByInduction1[n, f] is abbreviation for \
	ProveByInduction1[{n, 0}, f]. ";


(* these functions are provided in package types.M *)

integer::usage = 
	" integer[x] is True when the expression 'x' has an integral \
	value and is False otherwise. ";

Divisible::usage = 
	" Divisible[n, m] determines if 'n' is divisible by 'm'. ";

gcd::usage =
	" gcd[a, b] gives the greatest common divisor of 'a' and 'b'. ";

Even::usage = 
	" Even[x] is True if 'x' has an even value, False otherwise. ";

Odd::usage = 
	" Odd[x] is True if 'x' has an odd value and False otherwise. ";

real::usage = 
	" real[x] is used to determine if 'x' has a real value. ";

complex::usage = 
	" complex[x, y] is the constructor for complex numbers. Its value \
	is x + y I. ";

Rpart::usage =
	" Rpart[c] gives the real part of the complex number 'c'. ";

Ipart::usage =
	" Ipart[c] gives the imaginary part of the complex number 'c'. ";

i::usage =
	" i is the complex number Sqrt[-1]. ";


(* these functions are provided in the package inequality.M *)

Upper::usage =
	" Upper[f] gives a set of upper bounds for 'f'. ";

Lower::usage =
	" Lower[f] gives a set of lower bounds for 'f'. ";


(* these functions are provided in the package quantify.M *)

all::usage = 
	" all[x, f] is the universal quantifier, ('f' holds for all 'x'). \
	all[x, cond, f] is the restricted universal quantification \
	('f' holds for all 'x' satisfying 'cond'); consequently, \
	all[x, cond, f] is equivalent to all[x, cond -> f]. \
	all[{a, b, ..., c}, f] is an abbreviation for \
	all[a, all[b, ..., all[c, f]...]]. ";


some::usage = 
	" some[x, f] is the existential quantifier, ('f' holds for some \
	'x'). some[x, cond, f] is the restricted existential \
	quantification ('f' holds for some 'x' satisfying 'cond'); \
	consequently, some[x, cond, f] is equivalent to \
	some[x, cond & f]. some[{a, b, ..., c}, f] is an abbreviation for \
	some[a, some[b, ..., some[c, f]...]]. ";

congruent::usage =
	" congruent[a, b, c] decides if 'a' and 'b' are congruent \
	with respect 'c'. ";

over;
EndPackage[]