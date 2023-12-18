grammar extensibella:main:compose;

function buildExtThmProofs
IOVal<[String]> ::=
  --[(thm name, key relation, is host-y, bindings, body, key relation intros name)]
   thmsInfo::[(QName, RelationEnvItem, Boolean, Bindings, ExtBody, String)]
       --[(mod name, proof stuff grouped by all subgoals)]
   topGoalProofInfo::[(QName, [[(ProofState, [AnyCommand])]])]
   abella::ProcessHandle config::Configuration ioin::IOToken
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
  local intros_case_to_abella::IOVal<String> =
      sendBlockToAbella(intros_case, abella, ioin, config);

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
  local host_string::String =
      intros_case ++ "\n  " ++
      implode("\n  ", host_gathering.1);
  local host_to_abella::IOVal<String> =
      sendBlockToAbella(host_string, abella, intros_case_to_abella.io,
                        config);
  local host_rest::IOVal<[String]> =
      buildExtThmProofs(tail(thmsInfo), host_gathering.2, abella,
                        config, host_to_abella.io);

  --Extension Theorem Proof
  local ext_to_abella::IOVal<String> =
      --needs to use intros_case_to_abella for real
      sendCmdsToAbella(["skip."], abella, ioin, config);
  local ext_rest::IOVal<[String]> =
      buildExtThmProofs(tail(thmsInfo), topGoalProofInfo, abella,
                        config, ext_to_abella.io);

  return
      case thmsInfo of
      | [] -> ioval(ioin, [])
      | _::rest ->
        if fstThm.3
        then ioval(host_rest.io, host_string::host_rest.iovalue)
        else ioval(ext_rest.io, "skip."::ext_rest.iovalue)
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
