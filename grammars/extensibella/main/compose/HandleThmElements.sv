grammar extensibella:main:compose;

--modules and their remaining commands before handling this element
inherited attribute incomingMods::[(QName, DecCmds)] occurs on ThmElement;
--modules and their remaining commands after handling this element
synthesized attribute outgoingMods::[(QName, DecCmds)] occurs on ThmElement;
--commands to handle this element
synthesized attribute composedCmds::String occurs on ThmElement;

--pass in environments in MWDA-approved ways
inherited attribute relEnv::Env<RelationEnvItem> occurs on ThmElement;
inherited attribute constrEnv::Env<ConstructorEnvItem> occurs on ThmElement;
inherited attribute tyEnv::Env<TypeEnvItem> occurs on ThmElement;

aspect production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, var bindings, thm statement, induction measure, IH name)]
   thms::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   alsos::[(QName, Bindings, ExtBody, String, Maybe<String>)]
{
  local multiple::Boolean = length(thms) + length(alsos) > 1;
  local extName::QName =
      if multiple
      then toQName("$extThm_" ++ toString(genInt()))
      else fst(head(thms));
  local extThms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, String, Maybe<String>)
              rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, p.5, rest),
            endExtThms(), thms ++ alsos);
  extThms.relationEnv = top.relEnv;
  extThms.constructorEnv = top.constrEnv;
  extThms.typeEnv = top.tyEnv;
  extThms.expectedIHNum = 0;

  local declare::String =
      "Theorem " ++ extName.abella_pp ++ " : " ++
      extThms.toAbella.abella_pp ++ ".\n";
  local inductions::String =
      "induction on " ++
      implode(" ", map(toString, extThms.inductionNums)) ++ ".\n";
  local renames::String =
      implode(" ",
         map(\ p::(String, String, String) ->
               "rename " ++ p.1 ++ " to " ++ p.2 ++ ".",
             extThms.renamedIHs));

  local after::String =
      if multiple
      then "Split " ++ extName.abella_pp ++ " as " ++
           implode(", ",
                   map((.abella_pp),
                       map(fst, thms) ++ map(fst, alsos))) ++ ".\n"
      else "";

  top.composedCmds =
      declare ++ inductions ++ renames ++ " skip.\n" ++ after ++ "\n\n";


  top.outgoingMods =
      dropAllOccurrences(top.incomingMods, map(fst, thms));
}


aspect production translationConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
{
  --MWDA copy of body
  local bodyC::ExtBody = body;
  bodyC.relationEnv = top.relEnv;
  bodyC.constructorEnv = top.constrEnv;
  bodyC.typeEnv = top.tyEnv;
  bodyC.boundNames = binds.usedNames;

  local tcMods::[(QName, DecCmds)] =
      getAllOccurrences(top.incomingMods, [name]);
  --first contains declaration and set-up
  local startPrf::String =
      case head(tcMods).2 of
      | addRunCommands(c, _) ->
        --set-up for translation constraint, including declaration
        implode("", map((.abella_pp), c.toAbella))
      | _ -> error("Must be translationConstraint first")
      end;
  --rest of list provides the rest of the proof
  local restPrf::String =
      implode("", map(\ p::(QName, DecCmds) -> getProof(p.2).2,
                      tail(tcMods)));
  top.composedCmds = startPrf ++ " " ++ restPrf ++ "\n\n";

  --took these proofs, so drop them
  top.outgoingMods = dropAllOccurrences(top.incomingMods, [name]);
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  local declaration::String =
      "Theorem " ++ name.abella_pp ++
      (if null(params) then ""
                       else "[" ++ implode(", ", params) ++ "]") ++
      " : " ++ stmt.abella_pp ++ ".\n";

  local updatePair::([(QName, DecCmds)], String) =
      updateMod(top.incomingMods, name.moduleName, getProof);

  top.outgoingMods = updatePair.1;
  top.composedCmds = declaration ++ updatePair.2 ++ "\n\n";
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.composedCmds =
      "Split " ++ toSplit.abella_pp ++ " as " ++
      implode(", ", map((.abella_pp), newNames)) ++ ".\n\n";
  top.outgoingMods =
      updateMod(top.incomingMods, head(newNames).moduleName,
                \ c::DecCmds -> (dropFirstTopCommand(c), "")).1;
}


aspect production extIndElement
top::ThmElement ::=
   --[(rel name, rel arg names, trans args, trans ty,
   --    original, translated name)]
   rels::[(QName, [String], [Term], QName, String, String)]
{
  --need the definitions of R_ES and R_T;
  --maybe pull those out to the top for proof-level definitions?
  top.composedCmds = "%% Ext_Ind for " ++
      implode(", ", map((.abella_pp), map(fst, rels))) ++ "\n\n";
  top.outgoingMods =
      dropExtInd(top.incomingMods, map(fst, rels));
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
      | emptyRunCommands() -> error("dropFirstTopCommand(empty)")
      | addRunCommands(a, r) -> dropFirstTopCommand_help(r)
      end;
}
function dropFirstTopCommand_help
DecCmds ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> c
         | addRunCommands(anyTopCommand(t), r) -> c
         | addRunCommands(_, r) ->
           dropFirstTopCommand_help(r)
         end;
}


--get the next proof, dropping it from the cmds
--assumes it starts with one top command
function getProof
(DecCmds, String) ::= c::DecCmds
{
  return
      case c of
      | emptyRunCommands() -> error("getProof(empty)")
      | addRunCommands(a, r) -> getProof_help(r)
      end;
}
function getProof_help
(DecCmds, String) ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> (c, "")
         | addRunCommands(anyTopCommand(t), r) -> (c, "")
         | addRunCommands(anyProofCommand(p), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
           let f::ProofCommand = p.full
           in
             (rest.1, f.abella_pp ++ rest.2)
           end end
         | addRunCommands(anyNoOpCommand(n), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
             (rest.1, n.full.abella_pp ++ rest.2)
           end
         | addRunCommands(anyParseFailure(e), r) ->
           error("How did this get here?")
         end;
}


--get all the modules where thms is the first thing
function getAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, c)::getAllOccurrences(r, thms)
           | _ -> getAllOccurrences(r, thms)
           end
         end;
}


--drop the declaration and proof of thms in every module starting with them
function dropAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | emptyRunCommands() ->
             (q, c)::dropAllOccurrences(r, thms)
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, dropFirstTopCommand(c))::dropAllOccurrences(r, thms)
           | addRunCommands(a, _) ->
             (q, c)::dropAllOccurrences(r, thms)
           end
         end;
}
--same, but for Ext_Ind and Prove_Ext_Ind
function dropExtInd
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] rels::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | emptyRunCommands() ->
             (q, c)::dropExtInd(r, rels)
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesRels(rels) ->
             (q, dropFirstTopCommand(c))::dropExtInd(r, rels)
           | addRunCommands(a, _) ->
             (q, c)::dropExtInd(r, rels)
           end
         end;
}


--clear out all the non-proof things at the front of files
function dropNonProof
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)]
{
  return case mods of
         | [] -> []
         | (q, c)::r -> (q, dropNonProof_help(c))::dropNonProof(r)
         end;
}
function dropNonProof_help
DecCmds ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> c
         | addRunCommands(anyTopCommand(t), r) when t.isNotProof ->
           dropNonProof_help(dropFirstTopCommand(c))
         | _ -> c
         end;
}





{-
  Why an attribute pointing to a function instead of a set of
  attributes?  We're accessing this on decorated trees.  We cannot
  redecorate them to give them inherited attributes with the original
  map, so we use the functions to handle the actual work.
-}
--checks whether the given names are part of this one
synthesized attribute matchesNames::(Boolean ::= [QName])
   occurs on TopCommand;
--checks whether the given relations are part of this ExtInd
synthesized attribute matchesRels::(Boolean ::= [QName])
   occurs on TopCommand;

--false if a proof element, true otherwise
synthesized attribute isNotProof::Boolean occurs on TopCommand;

aspect default production
top::TopCommand ::=
{
  top.matchesRels = \ _ -> false;
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.matchesNames =
      \ l::[QName] ->
        !null(intersect(l, map(fst, thms.provingTheorems)));

  top.isNotProof = false;
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  top.matchesNames = \ l::[QName] -> !null(intersect(l, names));

  top.isNotProof = false;
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.matchesNames = \ l::[QName] -> head(l) == fullName;

  top.isNotProof = false;
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.matchesNames = \ l::[QName] -> head(l) == name;

  top.isNotProof = false;
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels =
      \ l::[QName] -> !null(intersect(l, body.relations));

  top.isNotProof = false;
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName]
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels = \ l::[QName] -> !null(intersect(rels, l));

  top.isNotProof = false;
}


aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.matchesNames = \ l::[QName] -> head(l) == fullName;

  top.isNotProof = false;
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  --won't use this for split, since that isn't distributed
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = false;
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}
