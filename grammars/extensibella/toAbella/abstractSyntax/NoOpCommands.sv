grammar extensibella:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp,
   toAbella<Maybe<NoOpCommand>>, --maybe because we might send nothing
   toAbellaMsgs,
   proverState;
propagate proverState, toAbellaMsgs on NoOpCommand;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text, other than our own debug option
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";

  top.toAbella =
      if opt == "debug" then nothing()
                        else just(setCommand(opt, val));

  top.toAbellaMsgs <-
      if opt == "debug"
      then if val == "on" || val == "ofF"
           then []
           else [errorMsg("Option 'debug' can only be set to " ++
                          "'on' or 'off', not '" ++ val ++ "'")]
      else if opt == "subgoals"
      then if val == "on" || val == "off" || toIntSafe(val).isJust
           then []
           else [errorMsg("Argument to option 'subgoals' must be " ++
                          "'on', 'off', or an integer; found '" ++
                          val ++ "'")]
      else if opt == "witnesses"
      then if val == "on" || val == "off"
           then []
           else [errorMsg("Argument to option 'witnesses' must be " ++
                          "'on' or 'off', not '" ++ val ++ "'")]
      else if opt == "search_depth"
      then if toIntSafe(val).isJust
           then []
           else [errorMsg("Argument to option 'search_depth' must " ++
                          "be integer; found '" ++ val ++ "'")]
      else [errorMsg("Unknown option '" ++ opt ++ "'")];
}


abstract production showCommand
top::NoOpCommand ::= theoremName::QName
{
  top.pp = "Show " ++ theoremName.pp ++ ".\n";

  local possibleThms::[(QName, Metaterm)] =
     findTheorem(theoremName, top.proverState);
  top.toAbella = just(top);

  top.toAbellaMsgs <-
      case possibleThms of
      | [] ->
        [errorMsg("Unknown theorem " ++ theoremName.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate theorem " ++ theoremName.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleThms))))]
      end;
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";

  top.toAbella = just(top);
}


--This is what Proof General uses for undoing things
abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = replicate(n - 1, "#back. ") ++ "#back.\n";

  top.toAbella = error("backCommand.toAbella");
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";

  top.toAbella = just(top);
}


abstract production showCurrentCommand
top::NoOpCommand ::=
{
  top.pp = "Show $$current.\n";

  top.toAbella = nothing();
}
