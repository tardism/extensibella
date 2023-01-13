grammar extensibella:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the language information.

  We do this in a separate file because the attributes here have to do
  with reading a file, not proving as we see in the other files.
-}



nonterminal ListOfCommands with
   pp, abella_pp,
   typeEnv, relationEnv, constructorEnv, proverState, currentModule,
   commandList, tys, rels, constrs,
   declaredThms;
propagate proverState, currentModule on ListOfCommands;

synthesized attribute commandList::[AnyCommand];

synthesized attribute tys::[TypeEnvItem];
synthesized attribute rels::[RelationEnvItem];
synthesized attribute constrs::[ConstructorEnvItem];

synthesized attribute declaredThms::[(QName, Metaterm)];


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.commandList = [];

  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.declaredThms = [];
}


abstract production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.pp = a.pp ++ rest.pp;
  top.abella_pp = a.abella_pp ++ rest.abella_pp;

  top.commandList = a::rest.commandList;

  top.tys = a.tys ++ rest.tys;
  top.rels = a.rels ++ rest.rels;
  top.constrs = a.constrs ++ rest.constrs;

  a.typeEnv = top.typeEnv;
  a.relationEnv = top.relationEnv;
  a.constructorEnv = top.constructorEnv;

  rest.typeEnv = addEnv(top.typeEnv, a.tys);
  rest.relationEnv = addEnv(top.relationEnv, a.rels);
  rest.constructorEnv = addEnv(top.constructorEnv, a.constrs);

  top.declaredThms = a.declaredThms ++ rest.declaredThms;
}





attribute
   tys, rels, constrs,
   declaredThms
occurs on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.tys = c.tys;
  top.rels = c.rels;
  top.constrs = c.constrs;

  --filter out anything containing dollar signs
  top.declaredThms =
      filter(\ p::(QName, Metaterm) ->
               indexOf("$", p.1.shortName) == -1,
             c.provingTheorems);
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.declaredThms = [];
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.declaredThms = [];
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.declaredThms = [];
}





attribute
   tys, rels, constrs
occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.tys =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | transQName(s) ->
                  [langTypeEnvItem(tyQName(s), 0,
                      foldr(addTypeList, emptyTypeList(),
                        --drop `ty -> ty -> prop` from end to get args
                         take(length(p.2.toList) - 3, p.2.toList)),
                      map(snd,
                          filter(\ inner::(QName, QName) ->
                                   p.1 == inner.1,
                                 defs.relationClauseModules)))]
                | _ -> []
                end,
              preds);
  top.rels =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | extQName(pc, s) ->
                  [extRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList),
                      pc, map(snd,
                              filter(\ inner::(QName, QName) ->
                                       p.1 == inner.1,
                                     defs.relationClauseModules)))]
                | transQName(_) -> []
                | _ ->
                  [fixedRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList))]
                end,
              fullNames);
  top.constrs = [];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.tys = []; --no tys from codefinitions
  top.rels =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | extQName(pc, s) ->
                  [extRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList),
                      pc, error("codefinitionDeclarationClauseModules"))]
                | transQName(_) -> []
                | _ ->
                  [fixedRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList))]
                end,
              preds);
  top.constrs = [];
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.tys =
      flatMap(\ q::QName ->
                case q of
                --get these from translation definitions
                | tyQName(s) -> []
                | _ -> [proofTypeEnvItem(q, k.len)]
                end,
              names);
  top.rels = [];
  top.constrs = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.tys = [];
  top.rels = [];
  top.constrs =
      map(constructorEnvItem(_,
             last(ty.toList),
             foldr(addTypeList, emptyTypeList(),
                   take(length(ty.toList) - 1, ty.toList))),
          names);
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}
