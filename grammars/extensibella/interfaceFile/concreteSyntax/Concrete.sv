grammar extensibella:interfaceFile:concreteSyntax;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:interfaceFile:abstractSyntax;


--have this for future proofing against changes adding extra elements
closed nonterminal Interface_c with ast<Interface>;

concrete productions top::Interface_c
| t::TopCommands_c
  { top.ast = interface(t.ast); }


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
