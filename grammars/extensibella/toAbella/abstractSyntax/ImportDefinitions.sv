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
   commandList, tys, rels, constrs;

synthesized attribute commandList::[AnyCommand];

synthesized attribute tys::[TypeEnvItem];
synthesized attribute rels::[RelationEnvItem];
synthesized attribute constrs::[ConstructorEnvItem];


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.commandList = [];

  top.tys = [];
  top.rels = [];
  top.constrs = [];
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
}


abstract production joinListOfCommands
top::ListOfCommands ::= l1::ListOfCommands l2::ListOfCommands
{
  top.pp = l1.pp ++ l2.pp;
  top.abella_pp = l1.abella_pp ++ l2.abella_pp;

  top.commandList = l1.commandList ++ l2.commandList;

  top.tys = l1.tys ++ l2.tys;
  top.rels = l1.rels ++ l2.rels;
  top.constrs = l1.constrs ++ l2.constrs;
}





attribute
   tys, rels, constrs
occurs on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.tys = c.tys;
  top.rels = c.rels;
  top.constrs = c.constrs;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
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
                         take(length(p.2.toList) - 3, p.2.toList)))]
                | _ -> []
                end,
              preds);
  top.rels =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | extQName(pc, s) ->
                  [extRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList),
                      pc)]
                | transQName(_) -> []
                | _ ->
                  [fixedRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList))]
                end,
              preds);
  top.constrs = [];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.tys =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | transQName(s) ->
                  [langTypeEnvItem(tyQName(s), 0,
                      foldr(addTypeList, emptyTypeList(),
                        --drop `ty -> ty -> prop` from end to get args
                         take(length(p.2.toList) - 3, p.2.toList)))]
                | _ -> []
                end,
              preds);
  top.rels =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | extQName(pc, s) ->
                  [extRelationEnvItem(p.1,
                      foldr(addTypeList, emptyTypeList(), p.2.toList),
                      pc)]
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
