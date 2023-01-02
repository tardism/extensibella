grammar extensibella:outerfaceFile:concreteSyntax;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:outerfaceFile:abstractSyntax;


--have this for future proofing against changes adding extra elements
closed nonterminal Outerface_c with ast<Outerface>;

concrete productions top::Outerface_c
| t::TopCommands_c
  { top.ast = outerface(t.ast); }


closed nonterminal TopCommands_c with ast<TopCommands>;

concrete productions top::TopCommands_c
|
  { top.ast = endTopCommands(); }
| t::PureTopCommand_c rest::TopCommands_c
  { top.ast =
        addTopCommands(
           case t.ast of
           | anyTopCommand(tc) -> tc
           | _ -> error("Cannot have errors in interface file")
           end, rest.ast); }
