grammar extensibella:toAbella:abstractSyntax;


abstract production extensibleTheoremDeclaration
top::TopCommand ::= depth::Integer thms::ExtThms
{
  top.pp = "Extensible_Theorem " ++ thms.pp ++ ".\n";

  top.toAbella = error("extensibleTheoremDeclaration.toAbella");

  top.builtNewProofState = error("extensibleTheoremDeclaration.builtNewProofState");

  top.provingTheorems = thms.provingTheorems;
}


abstract production proveObligations
top::TopCommand ::= names::[QName]
{
  top.pp = "Prove " ++ implode(", ", map((.pp), names)) ++ ".\n";

  top.toAbella = error("proveObligations.toAbella");
  --Need to check these are the right things to prove

  top.builtNewProofState = error("proveObligations.builtNewProofState");

  top.provingTheorems = error("proveObligations.provingTheorems");
}





nonterminal ExtThms with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState on ExtThms;

abstract production endExtThms
top::ExtThms ::=
{
  top.pp = "";

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];
}


abstract production addExtThms
top::ExtThms ::= name::QName body::ExtBody onLabel::String
                 rest::ExtThms
{
  top.pp = name.pp ++ " : " ++ body.pp ++ " on " ++ onLabel ++
           if rest.pp == "" then "" else " /\\ " ++ rest.pp;

  production fullName::QName =
      if name.isQualified
      then name
      else addQNameBase(top.currentModule, name.shortName);

  top.toAbella =
      case rest of
      | endExtThms() -> body.toAbella
      | _ -> andMetaterm(body.toAbella, rest.toAbella)
      end;

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
        foldr(\ p::(Maybe<String>, Decorated Metaterm) rest::[String] ->
                if p.1.isJust
                then p.1.fromJust::rest
                else makeUniqueNameFromBase("H", rest ++ labels)::rest,
              [], body.premises);

  top.toAbellaMsgs <-
      case lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                      a.isJust && b.isJust && a.fromJust == b.fromJust,
                    just(onLabel), body.premises) of
      | nothing() ->
        [errorMsg("Unknown label " ++ onLabel ++ " in extensible " ++
                  "theorem " ++ name.pp)]
      | just(m) ->
        [] --need to check the metaterm is built by an extensible relation
      end;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared predicate name " ++ name.pp ++
                    " does not have correct module (expected " ++
                    top.currentModule.pp ++ ")")]
      else [];

  top.provingTheorems = (fullName, body.thm)::rest.provingTheorems;
}





nonterminal ExtBody with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises, thm,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState on ExtBody;

--Decorated metaterm so we have the information from the envs
synthesized attribute premises::[(Maybe<String>, Decorated Metaterm)];
--Metaterm underlying the body
synthesized attribute thm::Metaterm;

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;

  top.thm = conc;

  top.toAbella = conc.toAbella;

  top.premises = [];
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = "(" ++ label ++ " : " ++ m.pp ++ ") -> " ++ rest.pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  top.premises = (just(label), m)::rest.premises;
}


abstract production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.pp = (if m.isAtomic then m.pp else "(" ++ m.pp ++ ")") ++
           " -> " ++ rest.pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  top.premises = (nothing(), m)::rest.premises;
}
