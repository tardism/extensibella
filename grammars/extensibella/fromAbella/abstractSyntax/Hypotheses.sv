grammar extensibella:fromAbella:abstractSyntax;



attribute
   inProof, hypList
occurs on ProofState;

aspect production proofInProgress
top::ProofState ::= subgoalNum::[Integer] currGoal::CurrentGoal futureGoals::[Subgoal]
{
  top.inProof = true;
  top.hypList = currGoal.hypList;
}


aspect production noProof
top::ProofState ::=
{
  top.inProof = false;
  top.hypList = [];
}


aspect production proofCompleted
top::ProofState ::=
{
  top.inProof = false;
  top.hypList = [];
}


aspect production proofAborted
top::ProofState ::=
{
  top.inProof = false;
  top.hypList = [];
}





attribute
   hypList
occurs on Hypothesis;

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.hypList = [(name, new(body))];
}

{-Going to disallow this, at least for now.
abstract production abbreviatedHyp
top::Hypothesis ::= name::String body::String
{
  top.pp = name ++ " : " ++ body;

  top.translation = abbreviatedHyp(name, body);
}-}





attribute
   hypList
occurs on Context;

aspect production emptyContext
top::Context ::=
{
  top.hypList = [];
}


aspect production singleContext
top::Context ::= h::Hypothesis
{
  top.hypList = h.hypList;
}


aspect production branchContext
top::Context ::= c1::Context c2::Context
{
  top.hypList = c1.hypList ++ c2.hypList;
}





attribute
   hypList
occurs on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  top.hypList = ctx.hypList;
}





--attribute occurs on Subgoal;

aspect production subgoal
top::Subgoal ::= num::[Integer] goal::Metaterm
{

}


aspect production hiddenSubgoals
top::Subgoal ::= num::Integer
{

}

