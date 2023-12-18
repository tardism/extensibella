grammar extensibella:main:compose;

function buildExtThmProofs
[String] ::=
  --[(thm name, key relation, is host-y, bindings, body, key relation intros name)]
   thmsInfo::[(QName, RelationEnvItem, Boolean, Bindings, ExtBody, String)]
       --[(mod name, proof stuff grouped by all subgoals)]
   topGoalProofInfo::[(QName, [[(ProofState, [AnyCommand])]])]
{
  local fstThm::(QName, RelationEnvItem, Boolean, Bindings,
                 ExtBody, String) = head(thmsInfo);

  local intros_case::String =
      let prems::[(Maybe<String>, Metaterm)] =
        decorate fstThm.5 with {
           typeEnv = error("typeEnv not needed");
           relationEnv = error("relationEnv not needed");
           constructorEnv = error("constructorEnv not needed");
           boundNames = fstThm.4.usedNames;
        }.premises
      in
        "intros " ++
        implode(" ",
           generateExtIntrosNames(catMaybes(map(fst, prems)),
              prems)) ++ ". " ++
        fstThm.6 ++ ": case " ++ fstThm.6 ++ " (keep)."
      end;

  --Host Theorem Proof
  --root number for subgoal for this thm
  local hostSubgoalNum::SubgoalNum =
      --module must exist, so .fromJust is valid
      let thisMod::[[(ProofState, [AnyCommand])]] =
          lookup(fstThm.1.moduleName, topGoalProofInfo).fromJust
      in --no empty lists in this, so head is valid
        subgoalRoot(head(head(thisMod)).1.currentSubgoal)
      end;
  --get commands, update remaining part
  local host_gathering::([String],
                         [(QName, [[(ProofState, [AnyCommand])]])]) =
      foldr(\ here::(QName, [[(ProofState, [AnyCommand])]])
              rest::([String],
                     [(QName, [[(ProofState, [AnyCommand])]])]) ->
              case here.2 of
              | ((s, _)::_)::_ when subgoalStartsWith(hostSubgoalNum,
                                       s.currentSubgoal) ->
                let sub::([[String]], [[(ProofState, [AnyCommand])]]) =
                    takeAllRootedBySubgoal(here.2, hostSubgoalNum)
                in
                  (implode("\n  ",
                      map(\ l::[String] -> implode(" ", l),
                          sub.1))::rest.1,
                   (here.1, sub.2)::rest.2)
                end
              | _ -> (rest.1, here::rest.2) --no proof here
              end,
            ([], []), topGoalProofInfo);

{-      foldr(\ here::(QName, [[(ProofState, [AnyCommand])]])
              rest::([String],
                     [(QName, [[(ProofState, [AnyCommand])]])]) ->
              case here.2 of
              | (((s, _)::_)::_)::_
                when subgoalStartsWith(hostSubgoalNum, s.currentSubgoal) ->
                (implode("\n  ",
                   map(\ l::[(ProofState, [AnyCommand])] ->
                         implode(" ", map((.abella_pp), flatMap(snd, l))),
                       head(here.2))
                   )::rest.1,
                 (here.1, tail(here.2))::rest.2)
              | _ -> (rest.1, here::rest.2) --no proof here
              end,
            ([], []), topGoalProofInfo);-}

  return
      case thmsInfo of
      | [] -> []
      | _::rest ->
        if fstThm.3
        then (intros_case ++ "\n  " ++
              implode("\n  ", host_gathering.1)
             )::buildExtThmProofs(rest, host_gathering.2)
        else "skip."::buildExtThmProofs(rest, topGoalProofInfo)
      end;
}


--get all the commands starting with a certain subgoal number, but
--   group them by subgoals under that
function takeAllRootedBySubgoal
([[String]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   root::SubgoalNum
{
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        let sub::([String], [[(ProofState, [AnyCommand])]]) =
            takeAllRooted(cmdStates, head(l).1.currentSubgoal)
        in
        let again::([[String]], [[(ProofState, [AnyCommand])]]) =
            takeAllRootedBySubgoal(sub.2, root)
        in
          (sub.1::again.1, again.2)
        end end
      | _ -> ([], cmdStates)
      end;
}


--get all the commands starting with a certain subgoal number, as well
--   as the remnant
--e.g. for numRoot = 1.1, gets commands for 1.1, 1.1.1, 1.1.3.1, but
--     not 1, 1.2, 3
function takeAllRooted
([String], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   numRoot::SubgoalNum
{
  local sub::([String], [[(ProofState, [AnyCommand])]]) =
      takeAllRooted(tail(cmdStates), numRoot);
  return
      case cmdStates of
      | x::rest when
        subgoalStartsWith(numRoot, head(x).1.currentSubgoal) ->
        (implode(" ", map((.abella_pp), flatMap(snd, x)))::sub.1,
         sub.2)
      | _ -> ([], cmdStates)
      end;
}
