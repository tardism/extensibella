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
  top.pp = "Prove " ++ implode(", ", names) ++ ".\n";

  top.toAbella = error("proveObligations.toAbella");
  --Need to check these are the right things to prove

  top.builtNewProofState = error("proveObligations.builtNewProofState");

  top.provingTheorems = error("proveObligations.provingTheorems");
}





nonterminal ExtThms with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState on ExtThms;

abstract production endExtThms
top::ExtThms ::=
{
  top.pp = "";

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];
}


abstract production addExtThms
top::ExtThms ::= name::String body::ExtBody onLabel::String
                 rest::ExtThms
{
  top.pp = name ++ " : " ++ body.pp ++ " on " ++ onLabel ++
           if rest.pp == "" then "" else " /\\ " ++ rest.pp;

  production fullName::QName = addBase(top.currentModule, name);

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
                  "theorem " ++ name)]
      | just(m) ->
        [] --need to check the metaterm is built by an extensible relation
      end;

  top.provingTheorems = (fullName, body)::rest.provingTheorems;
}





nonterminal ExtBody with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState on ExtBody;

--Decorated metaterm so we have the information from the envs
synthesized attribute premises::[(Maybe<String>, Decorated Metaterm)];

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;

  top.toAbella = conc.toAbella;

  top.premises = [];
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = "(" ++ label ++ " : " ++ m.pp ++ ") -> " ++ rest.pp;

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  top.premises = (just(label), m)::rest.premises;
}


abstract production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.pp = (if m.isAtomic then m.pp else "(" ++ m.pp ++ ")") ++
           " -> " ++ rest.pp;

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  top.premises = (nothing(), m)::rest.premises;
}
