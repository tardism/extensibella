grammar extensibella:main:compose;

{-
  Why an attribute pointing to a function instead of a set of
  attributes?  We're accessing this on decorated trees.  We cannot
  redecorate them to give them inherited attributes with the original
  map, so we use the functions to pass in the appropriate arguments,
  then let the functions handle the actual work.
-}
synthesized attribute
                  --updated map        proof text   original map
   handleElement::(([(QName, DecCmds)], String) ::= [(QName, DecCmds)])
   occurs on ThmElement;

aspect production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, var bindings, thm statement, induction measure, IH name)]
   thms::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   alsos::[(QName, Bindings, ExtBody, String, Maybe<String>)]
{
  top.handleElement = handleExtensibleMutualTheoremGroup(_, thms, alsos);
}


aspect production translationConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
{
  top.handleElement = handleTranslationConstraint(_, name, binds, body);

  top.matchesNames = \ l::[QName] -> head(l) == name;
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  top.handleElement = handleNonextensibleTheorem(_, name, params, stmt);

  top.matchesNames = \ l::[QName] -> head(l) == name;
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.handleElement = handleSplit(_, toSplit, newNames);

  top.matchesNames = \ l::[QName] -> false;
}


aspect production extIndElement
top::ThmElement ::=
   --[(rel name, rel arg names, trans args, trans ty,
   --    original, translated name)]
   rels::[(QName, [String], [Term], QName, String, String)]
{
  top.handleElement = handleExtInd(_, rels);

  top.matchesNames =
      \ l::[QName] -> !null(intersect(l, map(fst, rels)));
}





----------------------------------------------------------------------
-- Functions to handle different types of theorem elements
----------------------------------------------------------------------

function handleExtensibleMutualTheoremGroup
([(QName, DecCmds)], String) ::=
   mods::[(QName, DecCmds)]
   --[(thm name, var bindings, thm statement, induction measure, IH name)]
   thms::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   alsos::[(QName, Bindings, ExtBody, String, Maybe<String>)]
{
  return error("");
}


function handleTranslationConstraint
([(QName, DecCmds)], String) ::=
   mods::[(QName, DecCmds)] name::QName binds::Bindings body::ExtBody
{
  local declare::String =
      "Theorem " ++ name.abella_pp ++ " : " ++
      "forall " ++ binds.abella_pp ++ ",\n" ++
      body.abella_pp ++ ".\n";
  local startPrf::String =
      "induction on 1. skip.\n\n"; --fill in for real later
  local removed::[(QName, DecCmds)] = dropAllOccurrences(name);
  return (removed, declare ++ startPrf);
}


function handleNonextensibleTheorem
([(QName, DecCmds)], String) ::=
   mods::[(QName, DecCmds)] name::QName params::[String] stmt::Metaterm
{
  return updateMod(mods, name.moduleName, getProof);
}


function handleSplit
([(QName, DecCmds)], String) ::=
   mods::[(QName, DecCmds)] toSplit::QName allNames::[QName]
{
  local cmd::String =
      "Split " ++ toSplit.abella_pp ++ " as " ++
      implode(", ", map((.abella_pp), allNames)) ++ ".\n\n";
  local outMods::[(QName, DecCmds)] =
      updateMod(mods, head(allNames).moduleName,
                \ c::DecCmds -> (dropFirstTopCommand(c), "")).1;
  return (outMods, cmd);
}


function handleExtInd
([(QName, DecCmds)], String) ::=
   mods::[(QName, DecCmds)]
   --[(rel name, rel arg names, trans args, trans ty,
   --    original, translated name)]
   rels::[(QName, [String], [Term], QName, String, String)]
{
  --remember this also needs to generate R_P, R_{ES}, and dropP(R)
  return error("");
}





----------------------------------------------------------------------
-- Helper functions
----------------------------------------------------------------------

--update a module in the list with the update function, returning the
--   produced string
--does not change the order of modules, just updates one
function updateMod
([(QName, DecCmds)], String) ::= mods::[(QName, DecCmds)] mod::QName
                                 update::((DecCmds, String) ::= DecCmds)
{
  return case mods of
         | [] -> error("Module not in module map")
         | (q, c)::rest when q == mod ->
           let p::(DecCmds, String) = update(c)
           in
             ((q, p.1)::rest, p.2)
           end
         | (q, c)::rest ->
           let p::([(QName, DecCmds)], String) =
               updateMod(rest, mod, update)
           in
             ((q, c)::p.1, p.2)
           end
         end;
}


--drop the first top command in a sequence of commands, including its
--   proof if it has one
--assumes the commands start with a top command
function dropFirstTopCommand
DecCmds ::= c::DecCmds
{
  return
      case c of
      | emptyListOfCommands() -> error("dropFirstTopCommand(empty)")
      | addListOfCommands(_, r) -> dropFirstTopCommand_help(r)
      end;
}
function dropFirstTopCommand_help
DecCmds ::= c::DecCmds
{
  return case c of
         | emptyListOfCommands() -> c
         | addListOfCommands(anyTopCommand(t), r) -> c
         | addListOfCommands(anyProofCommand(p), r) ->
           dropFirstTopCommand_help(r)
         | addListOfCommands(anyNoOpCommand(n), r) ->
           dropFirstTopCommand_help(r)
         | addListOfCommands(anyParseFailure(e), r) ->
           error("How did this get here?")
         end;
}


--get the next proof, dropping it from the cmds
--assumes it starts with one top command
function getProof
(DecCmds, String) ::= c::DecCmds
{
  return
      case c of
      | emptyListOfCommands() -> error("getProof(empty)")
      | addListOfCommands(_, r) -> getProof_help(r)
      end;
}
function getProof_help
(DecCmds, String) ::= c::DecCmds
{
  return case c of
         | emptyListOfCommands() -> (c, "")
         | addListOfCommands(anyTopCommand(t), r) -> (c, "")
         | addListOfCommands(anyProofCommand(p), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
             (rest.1, p.abella_pp ++ rest.2)
           end
         | addListOfCommands(anyNoOpCommand(n), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
             (rest.1, n.abella_pp ++ rest.2)
           end
         | addListOfCommands(anyParseFailure(e), r) ->
           error("How did this get here?")
         end;
}


--drop the whole thing every time proving it comes up
--this is only to get to testing basics faster
function dropAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | emptyListOfCommands() ->
             (q, c)::dropAllOccurrences(r, thms)
           | addListOfCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, dropFirstTopCommand(c))::dropAllOccurrences(r, thms)
           | addListOfCommands(_) ->
             (q, c)::dropAllOccurrences(r, thms)
           end
         end;
}





--checks whether the given names are part of this one
synthesized attribute matchesNames::(Boolean ::= [QName])
   occurs on TopCommand;

aspect production extensibleTheorem
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.matchesNames =
      \ l::[QName] -> !null(intersect(l, map(fst, thms)));
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{

}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{

}


aspect production proveConstraint
top::TopCommand ::= name::QName
{

}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{

}


aspect production proveExtInd
top::TopCommand ::= rels::[QName]
{

}


aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{

}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{

}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{

}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{

}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{

}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{

}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{

}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{

}


aspect production importCommand
top::TopCommand ::= name::String
{

}
