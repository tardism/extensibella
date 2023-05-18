grammar extensibella:common:abstractSyntax;

synthesized attribute hypList::[(String, Metaterm)];
synthesized attribute currentSubgoal::SubgoalNum;

nonterminal ProofState with
   pp,
   hypList, currentSubgoal, goal,
   inProof,
   typeEnv, constructorEnv, relationEnv,
   usedNames;
propagate typeEnv, constructorEnv, relationEnv on ProofState;

synthesized attribute inProof::Boolean;

abstract production proofInProgress
top::ProofState ::= subgoalNum::SubgoalNum currGoal::CurrentGoal
                    futureGoals::[Subgoal]
{
  local subgoalPP::Document =
      if subgoalNum != initialSubgoalNum
      then cat(text("Subgoal " ++ subgoalNumToString(subgoalNum) ++
                    ":"), realLine())
      else text("");
  top.pp = ppConcat([subgoalPP, realLine(), currGoal.pp, realLine(),
                     ppImplode(cat(realLine(), realLine()),
                               map((.pp), futureGoals))]);

  top.hypList = currGoal.hypList;

  top.currentSubgoal = subgoalNum;
  top.goal = currGoal.goal;

  top.inProof = true;
}


abstract production noProof
top::ProofState ::=
{
  top.pp = text("");

  top.hypList = [];

  top.currentSubgoal = [];

  top.goal = nothing();

  top.inProof = false;
}


abstract production proofCompleted
top::ProofState ::=
{
  top.pp = text("Proof completed.");

  top.hypList = [];

  top.currentSubgoal = [];

  top.goal = nothing();

  top.inProof = false;

  forwards to noProof();
}


abstract production proofAborted
top::ProofState ::=
{
  top.pp = text("Proof ABORTED.");

  top.hypList = [];

  top.currentSubgoal = [];

  top.goal = nothing();

  top.inProof = false;

  forwards to noProof();
}



nonterminal CurrentGoal with
   pp,
   hypList, goal,
   typeEnv, constructorEnv, relationEnv,
   usedNames;
propagate typeEnv, constructorEnv, relationEnv on CurrentGoal;

abstract production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  local varsPP::Document =
        if null(vars)
        then text("")
        else ppConcat([text("Variables: "),
                ppImplode(text(" "), map(text, vars)), realLine()]);
  top.pp = ppConcat([varsPP,
                     ppImplode(realLine(), ctx.pps),
                     text("============================"), realLine(),
                     text(" "), goal.pp, realLine()]);

  top.hypList = ctx.hypList;

  top.goal = just(new(goal));

  ctx.boundNames = vars;
  goal.boundNames = vars;
}



--A context is the hypotheses available for proving the current goal
nonterminal Context with
   pps, hypList,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv on Context;
propagate boundNames on Context;

abstract production emptyContext
top::Context ::=
{
  top.pps = [];

  top.hypList = [];
}


abstract production singleContext
top::Context ::= h::Hypothesis
{
  top.pps = h.pps;

  top.hypList = h.hypList;
}


abstract production branchContext
top::Context ::= c1::Context c2::Context
{
  top.pps = c1.pps ++ c2.pps;

  top.hypList = c1.hypList ++ c2.hypList;
}



nonterminal Hypothesis with
   pps, --more of a maybe than a list
   hypList,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv on Hypothesis;
propagate boundNames on Hypothesis;

abstract production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.pps = [ppConcat([text(name), text(" : "),
                       --indent it so it is further over than "name : "
                       nest(length(name) + 3, body.pp)])];

  top.hypList = [(name, new(body))];
}



--A subgoal is a goal to proven in the future, after the current goal
nonterminal Subgoal with pp, typeEnv, relationEnv, constructorEnv;
propagate typeEnv, relationEnv, constructorEnv on Subgoal;

type SubgoalNum = [Integer];

abstract production subgoal
top::Subgoal ::= num::SubgoalNum goal::Metaterm
{
  top.pp =
      ppConcat([text("Subgoal " ++ subgoalNumToString(num) ++ " is:"),
                realLine(), text(" "), goal.pp]);
}


abstract production hiddenSubgoals
top::Subgoal ::= num::Integer
{
  top.pp = text(toString(num) ++ " other subgoal" ++
                (if num == 1 then "." else "s."));
}











global initialSubgoalNum::SubgoalNum = [0];


function subgoalNumToString
String ::= subgoalNum::SubgoalNum
{
  return case subgoalNum of
         | [] -> error("Subgoal numbers should not be empty")
         | [x] -> toString(x)
         | h::t -> toString(h) ++ "." ++ subgoalNumToString(t)
         end;
}


--s1 < s2
--true if some position (from left) in s1 is less than corresponding
--   in s2 or s1 runs out first
function subgoalLess
Boolean ::= s1::SubgoalNum s2::SubgoalNum
{
  return
     case s1, s2 of
     | h1::tl1, h2::tl2 ->
       if h1 < h2
       then true
       else if h1 == h2
            then subgoalLess(tl1, tl2)
            else false
     | [], _::_ -> true
     | _::_, [] -> false
     | [], [] -> false
     end;
}


--Comparing (possibly empty) subgoals to see if a goal was completed
function subgoalCompleted
Boolean ::= oldSubgoal::SubgoalNum newSubgoal::SubgoalNum
{
  --Catch a subgoal completing and going forward to another one
  local goalToNewGoal::Boolean =
        subgoalLess(oldSubgoal, newSubgoal) &&
        --need to check length to avoid catching e.g. [2] expanding to [2.1]
        ( length(oldSubgoal) == length(newSubgoal) ||
          length(oldSubgoal) > length(newSubgoal) );
  --Catch a subgoal completing and going back to the previous one
  local goalToPreviousGoal::Boolean =
        subgoalLess(newSubgoal, oldSubgoal);
  --Catch expanding [0]
  --Either finishing the whole proof or expanding to subgoals
  local isSubgoal0::Boolean =
        case oldSubgoal of
        | [0] -> true
        | _ -> false
        end;
  return
     ! null(oldSubgoal) &&
     ( goalToNewGoal ||
       goalToPreviousGoal ) &&
     ! isSubgoal0;
}

