grammar extensibella:fromAbella:abstractSyntax;



attribute
   fromAbella<ProofState>,
   inProof, hypList
occurs on ProofState;

aspect production proofInProgress
top::ProofState ::= subgoalNum::[Integer] currGoal::CurrentGoal
                    futureGoals::[Subgoal]
{
  top.fromAbella =
      proofInProgress(subgoalNum, currGoal.fromAbella, futureGoals);

  top.inProof = true;
  top.hypList = currGoal.hypList;
}


aspect production noProof
top::ProofState ::=
{
  top.fromAbella = noProof();

  top.inProof = false;
  top.hypList = [];
}


aspect production proofCompleted
top::ProofState ::=
{
  top.fromAbella = proofCompleted();

  top.inProof = false;
  top.hypList = [];
}


aspect production proofAborted
top::ProofState ::=
{
  top.fromAbella = proofAborted();

  top.inProof = false;
  top.hypList = [];
}





attribute
   fromAbella<Hypothesis>,
   hypList
occurs on Hypothesis;

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.fromAbella = metatermHyp(name, body.fromAbella);

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
   fromAbella<Context>,
   hypList
occurs on Context;

aspect production emptyContext
top::Context ::=
{
  top.fromAbella = emptyContext();

  top.hypList = [];
}


aspect production singleContext
top::Context ::= h::Hypothesis
{
  top.fromAbella = singleContext(h.fromAbella);

  top.hypList = h.hypList;
}


aspect production branchContext
top::Context ::= c1::Context c2::Context
{
  top.fromAbella = branchContext(c1.fromAbella, c2.fromAbella);

  top.hypList = c1.hypList ++ c2.hypList;
}





attribute
   fromAbella<CurrentGoal>,
   hypList
occurs on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  top.fromAbella = currentGoal(vars, ctx.fromAbella, goal.fromAbella);

  top.hypList = ctx.hypList;
}





attribute
   fromAbella<Subgoal>
occurs on Subgoal;

aspect production subgoal
top::Subgoal ::= num::[Integer] goal::Metaterm
{
  top.fromAbella = subgoal(num, goal.fromAbella);
}


aspect production hiddenSubgoals
top::Subgoal ::= num::Integer
{
  top.fromAbella = hiddenSubgoals(num);
}

