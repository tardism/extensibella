grammar extensibella:main:util;

--We will use the parsed command line arguments as a way to pass along
--information about how things ought to run, so we give it a name:
type Configuration = Decorated CmdArgs;


--We pass along the Configuration so it can be used further down
inherited attribute config::Configuration;


attribute
   config
occurs on ListOfCommands, AnyCommand;

aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  a.config = top.config;
  rest.config = top.config;
}
