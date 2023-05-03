grammar extensibella:common:abstractSyntax;


function containsAssociated
Boolean ::= s::String l::[(String, a)]
{
  return
     case l of
     | [] -> false
     | (s2, _)::_ when s2 == s -> true
     | _::tl -> containsAssociated(s, tl)
     end;
}


function splitList
Pair<[a] [b]> ::= l::[Pair<a b>]
{
  return case l of
         | [] -> pair([], [])
         | pair(a, b)::rest ->
           case splitList(rest) of
           | pair(la, lb) -> pair(a::la, b::lb)
           end
         end;
}


function zipLists
[(a, b)] ::= l1::[a] l2::[b]
{
  return
     case l1, l2 of
     | [], _ -> []
     | _, [] -> []
     | h1::t1, h2::t2 -> (h1, h2)::zipLists(t1, t2)
     end;
}


function elemAtIndex
a ::= l::[a] i::Integer
{
  return
     case l of
     | [] -> error("Index too deep")
     | h::t ->
       if i == 0
       then h
       else elemAtIndex(t, i - 1)
     end;
}



{-
  Find the values associated with a key, where the key occurs in the
  middle of a triple
-}
function findAssociatedMiddle
Maybe<(a, b)> ::= key::String container::[(a, String, b)]
{
  return
     case container of
     | [] -> nothing()
     | (a, s, b)::_ when s == key ->
       just((a, b))
     | _::tl -> findAssociatedMiddle(key, tl)
     end;
}



{-
  Find the value associated with a key, either in a single list or in
  a nested list of scopes.
-}
function findAssociated
Maybe<a> ::= key::String container::[Pair<String a>]
{
  return case container of
         | [] -> nothing()
         | pair(a, b)::tl -> if key == a
                             then just(b)
                             else findAssociated(key, tl)
         end;
}

function findAssociatedScopes
Maybe<a> ::= key::String scopes::[[Pair<String a>]]
{
  return case scopes of
         | [] -> nothing()
         | scope::rest ->
           case findAssociated(key, scope) of
           | just(x) -> just(x)
           | nothing() -> findAssociatedScopes(key, rest)
           end
         end;
}




{-
  Replace the value associated with a key with the new value, either
  in a single list or in a nested list of scopes.
  - The scopes version assumes the key is contained in some scope.
-}
function replaceAssociated
Maybe<[(String, a)]> ::= key::String newVal::a container::[(String, a)]
{
  return case container of
         | [] -> nothing()
         | (a, b)::tl ->
           if key == a
           then just((a, newVal)::tl)
           else case replaceAssociated(key, newVal, tl) of
                | just(newtl) -> just((a, b)::newtl)
                | nothing() -> nothing()
                end
         end;
}

function replaceAssociatedScopes
[[Pair<String a>]] ::= key::String newVal::a scopes::[[Pair<String a>]]
{
  return case scopes of
         | [] -> [] --error for an unknown name
         | currentScope::rest ->
           case replaceAssociated(key, newVal, currentScope) of
           | just(newScope) -> newScope::rest
           | nothing() -> currentScope::replaceAssociatedScopes(key, newVal, rest)
           end
         end;
}


{-
  Check the first character in the given string is a capitalized letter
-}
function isCapitalized
Boolean ::= str::String
{
  return str != "" && isUpper(substring(0, 1, str));
}




function toTypeList
TypeList ::= tys::[Type]
{
  return foldr(addTypeList, emptyTypeList(), tys);
}
function toTermList
TermList ::= tms::[Term]
{
  return foldr(consTermList, emptyTermList(), tms);
}
function toBindings
Bindings ::= names::[String]
{
  return
     if null(names) then error("toBindings([])")
     else foldrLastElem(addBindings(_, nothingType(), _),
                        oneBinding(_, nothingType()), names);
}




function freshName
String ::= base::String used::[String]
{
  local reservedWords::[String] =
      ["Module", "Close", "CoDefine", "Define", "Kind", "Query",
       "Quit", "Set", "Show", "Split", "Theorem", "Type", "Prove"];
  return if contains(base, reservedWords ++ used)
         then freshName_help(base, 1, reservedWords ++ used)
         else base;
}
function freshName_help
String ::= base::String index::Integer used::[String]
{
  return if contains(base ++ toString(index), used)
         then freshName_help(base, index + 1, used)
         else base ++ toString(index);
}




{-
  Error for when something is yet to be completed
-}
function todoError
a ::= s::String
{
  return error("TODO:  " ++ s);
}
