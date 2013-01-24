(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* Functions shared by different packages *)

BeginPackage["SystemInterface`"]


(* these functions are provided in package simplify.M *)

NIL::usage =
	" NIL denotes True in a conjunction, False in a disjunction. ";

SimplifyMessage::usage =
	" SimplifyMessage is a list of rules and formulas which are \
	results of intermediate steps of simplification. "

SimplifyIfChanged::usage =
	" SimplifyIfChanged[f1, f2] gives StrongSimplify[f2] as answer \
	if f1 is not the same as f2, otherwise return f2. ";

RulesFrom::usage =
	" RulesFrom[f] gives a list of simplification rules derived from\
	'f'. ";


(* these functions are provided in package environment.M *)


VariablesIn::usage =
	" VariablesIn[f] gives a list of all Variables appears in 'f'. ";

TermsIn::usage =
	" TermsIn[a] gives a list of basic terms appeared in 'a'. ";

BasicTerms::usage = 
	" BasicTerms is a list of the basic terms used so far. ";

NumberOfTerms::usage = 
	" NumberOfTerms gives the number of basic terms used so far. ";

TermNumber::usage =
	" TermNumber[f] gives the index of f in the basic term list, if \
	f is not yet in the basic term list, add f to it. ";

NumberOfAppearances::usage =
	" NumberOfAppearance[f, pattern] gives the number of different \
	appearance of 'pattern' in formula 'a'. ";

Appearances::usage =
	"Appearances[f, pattern] gives a list containing different \
	appearances of pattern in formula 'a'. ";

KnownUpper::usage = 
	" KnownUpper[[n]] is Unknown if the upper bound of the nth basic \
	term is unknown, otherwise is the upper bound of that term. ";

KnownLower::usage = 
	" KnownLower[[n]] is Unknown if the lower bound of the nth basic \
	term is unknown, otherwise is the lower bound of that term. ";

Unknown::usage = 
	" Unknown is the symbol denoting the unknown bounds. ";


GivenIdentities::usage =
	" GivenIdentities is a list of given identities accessable in the \
	current context section. ";

GivenUpper::usage =
	" GivenUpper[f] gives the sat of given upper bounds for 'f'. ";

GivenLower::usage =
	" GivenLower[f] gives the sat of given lower bounds for 'f'. ";

RulesFromGiven::usage =
	" RulesFromGiven is a list of rewrite rules derived from the \
	given properties. ";

EvaluateAssuming::usage = 
	" EvaluateAssuming[cond, f] evaluates 'f' assuming 'cond' is \
	true. ";

UserFunctions::usage =
	" UserFunctions is a list of rewrite rules which replace the \
	appearances of user defined functions by their definition. ";

GivenFormulas::usage =
	" GivenFormulas is a list of given properties which can be seen \
	using PrintGiven. "


(* these functions are provided in package inequality.M *)

ProveUsingBound::usage =
	" ProveUsingBound[s] tries to prove sequent 's' by replacing \
	expressions appears in inequalities by their upper or lower \
	bounds. ";

Strict::usage =
	" Strist[a] is an upper(lower) bound of some formula 'f' means \
	'a' is a strict upper(lower) bound for 'f'. ";

InequalityRules::usage =
	" InequalityRules is a set of rules about inequalities. ";

RulesForRelations::usage =
	" RulesForRelation is a set of rules that can decide the truth values \
	of some equations and inequalities. ";

DepthCount::usage = 
	" DepthCount is the current depth for using bound to prove 
	inequalities. ";


(* these functions are provided in package equation.M *)

EquationRules::usage =
	" EquationRules is a set of rules about equations. ";

SolveEquation::usage =
	" SolveEquation[f] tries to solve the linear equations appears \
	in 'f'. ";

SubstEquation::usage =
	" SubstEquation[f] rewrites 'f' by substitute terms with their \
	equivalents. ";


(* these functions are provided in package rewrite.M *)

OpenDefinition::usage =
	" OpenDefinition[f] replaces the user defined functions in 'f' \
	by their definitions. ";

Rewriting::usage =
	" Rewriting[f] rewrites 'f' use the user defined rules. ";

Factorize::usage =
	" Factorise[f] replace \" a R b \" with \" Factor[a-b] R 0 \", \
	where R is either ==, <= or <. ";


(* these functions are provided in package quantify.M *)


substitution::usage = 
	" substitution[{x1 -> t1, ..., xn -> tn}] is the instantiation \
	of substitute x1 with t1, ..., xn with tn ";

Var::usage =
	" Var[v] is the skolem notation for an existentially quantified \
	variable. ";

Const::usage =
	" Const[v, vars] is the skolem notation for an universally \
	quantified variable, where vars are some skolem variables. ";

Skolemize::usage =
	" Skolemize[f, position] renames bound variables in 'f'. \
	'position' specifies the position of 'f' in a sequent, \
	'PositivePosition' denotes the positive position, 'NegativePosition' \
	denates the negative position. ";

Requantify::usage =
	" Requantify[position, f] adds quantifications back to 'f', \
	so it can be printed out in a quantified form. 'position' \
	denotes the position of 'f', it can be NegativePosition or \
	PositivePosition. ";

PositivePosition::usage =
	" PositivePosition means the positive position in a sequent. 
	(See also quantify) ";

NegativePosition::usage =
	" NegativePosition means the negative position in a sequent. \
	(See also quantify) ";

unify::usage =
	" unify[f1, f2] tries to match 'f1' and 'f2', return with the \
	unifier. ";

apply::usage =
	" apply[u, f] applies instantiation 'u' to 'f'. ";

CurrentLemma::usage =
	" CurrentLemma is the lemma is being used. It only works when \
	trying to using the lemmas or facts. ";

MatchingState::usage =
	" MatchingState shows the current rule while unification is \
	used. ";

conjunct::usage =
	" conjunct[f1, f2] shows if 'f2' matches a conjunct of 'f1'. ";

disjunct::usage =
	" disjunct[f1, f2] shows if a disjunct of 'f2' matches a conjunct \
	of 'f1'. ";


(* these functions are provided in package functions.M *)

AbsRule::usage =
	" AbsRule is a local rule about absolute values, it is used in \
	simplification. ";

MaxMinRules::usage =
	" MaxMinRules is a set of local rules about maximum or minimum \
	values, it is used in simplification. ";

GosperSum::usage = "GosperSum[term, {var, n0, n1}] attempts to find the value 
	of Sum[term, {var, n0, n1}] for symbolic n0, n1."

SimplifySummation::usage =
	" SimplifySummation[i][f] tries ith method to simplify the summation \
	expressions appears in 'f'. ";

SimplifyProduct::usage =
	" SimplifyProduct[f] tries to simplify the product expressions \
	appears in 'f'. ";

SimplifyLimit::usage =
	" SimplifyLimit[f] tries to simplify the limit expressions \
	appears in 'f'. ";

RewriteTrig::usage =
	" RewriteTrig[s] rewrites the trigonometric expressions appeared \
	in 's'. ";

RewriteSum::usage =
	" RewriteSum[s] rewrites the summation expressions appeared \
	in 's'. ";

TrigSimplify::usage =
	" TrigSimplify[s] rewrites the trigonometric expressions \
	appears in 's'. ";


(* these functions are provided in package prover.M *)

BranchStack::usage =
	" BranchStack consists of the unreached theorem branches with is \
	generated in and-split or cases. ";

PrintMessage::usage =
	" PrintMessage[message] prints out 'message', which is generated \
	in simplification. ";

PrintResult::usage =
	" PrintResult[rule, result] prints both the result and the rule \
	used to achieve that. ";

PrintSequent::usage =
	" PrintSequent[s] prints out sequent 's'. ";

PrintSequent1::usage =
	" PrintSequent[s] prints out sequent 's'. ";

PrintLemma::usage =
	" PrintLemma[l] prints out lemma 'l'. ";

print::usage =
	" print[s1, s2, ..., sn] prints the joint of some strings. ";

print1::usage =
	" print[s1, s2, ..., sn] prints the joint of some strings. ";

SucceedWith::usage =
	" SucceedWith[f] tries to retain only the success steps during \
	the proof. ";

TryOtherBranches::usage =
	" TryOtherBranches[u] finishes the current proving branch, and \
	try to prove other branches with an instantiation 'u' get during \
	the proof of current branch. ";

orelse::usage =
	" orelse[f1, f2, ..., fn] evaluates the formulas sequentially, \
	return the first non-False as result, if all of them are False, \
	return with False. ";

TryProving::usage =
	" TryProving[s] tries to prove a sequent 's'. ";

FalseQ::usage =
	" FalseQ[f] gives True if 'f' is False, False otherwise. ";


EndPackage[]
