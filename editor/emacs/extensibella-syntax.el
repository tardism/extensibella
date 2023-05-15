
(provide 'extensibella-syntax)


(defconst extensibella-top-commands
  '(
    ;;The actual top commands
    ;; Theorem | Define | Import | Kind | Split | Type | Extensible_Theorem | Module | Prove | Translation_Constraint
    ("\\<\\(\\(Theorem\\)\\|\\(Define\\)\\|\\(Import\\)\\|\\(Kind\\)\\|\\(Split\\)\\|\\(Type\\)\\|\\(Extensible_Theorem\\)\\|\\(Module\\)\\|\\(Prove\\)\\|\\(Translation_Constraint\\)\\|\\(Prove_Constraint\\)\\|\\(Ext_Ind\\)\\|\\(Prove_Ext_Ind\\)\\)\\>"
     . font-lock-keyword-face)
    ;;Auxiliary words to go with them
    ;; as | by
    ("\\<\\(\\(as\\)\\|\\(by\\)\\)\\>"
     . font-lock-keyword-face)
    ;;Highlighting types
    ("\\<\\(type\\)\\>"
     . font-lock-type-face)
    )
  )
(defconst extensibella-common-commands
  '(
    ;; Set | Show
    ("\\<\\(\\(Set\\)\\|\\(Show\\)\\)\\>"
     . font-lock-keyword-face)
    ;;We want this to stand out, since it doesn't belong in scripts
    ("\\<\\(Quit\\)\\>"
     . font-lock-warning-face)
    )
  )
(defconst extensibella-proof-commands
  '(
    ;;The actual proof commands (minus exists)
    ;; apply | assert | backchain | case | clear | induction | intros | left |
    ;; rename | right | search | split | split* | unfold |
    ;; witness | in | with
    ("\\<\\(\\(apply\\)\\|\\(assert\\)\\|\\(backchain\\)\\|\\(case\\)\\|\\(clear\\)\\|\\(induction\\)\\|\\(intros\\)\\|\\(left\\)\\|\\(rename\\)\\|\\(right\\)\\|\\(search\\)\\|\\(split\\)\\|\\(split*\\)\\|\\(unfold\\)\\|\\(witness\\)\\|\\(in\\)\\|\\(with\\)\\)\\>"
     . font-lock-function-name-face)
    ;;Auxiliary words to go with them
    ;; keep | on | to
    ("\\<\\(\\(keep\\)\\|\\(on\\)\\|\\(to\\)\\)\\>"
     . font-lock-function-name-face)
    ;;Commands which we don't want to have appear
    ;; skip | abort | #back | #reset | undo
    ("\\<\\(\\(skip\\)\\|\\(abort\\)\\|\\(#back\\)\\|\\(#reset\\)\\|\\(undo\\)\\)\\>"
     . font-lock-warning-face)
    )
  )
(defconst extensibella-comments
  '(
    ;;Line comments
    ("%.*"
     . font-lock-comment-face)
    )
  )

(defconst extensibella-logic
  '(
    ;; forall | exists | nabla
    ("\\<\\(\\(forall\\)\\|\\(exists\\)\\|\\(nabla\\)\\)\\>"
     ;;This needs to use font-lock-keyword-face because 'exists' is in
     ;;both this and proof commands
     . font-lock-keyword-face)
    ;; true | false
    ("\\<\\(\\(true\\)\\|\\(false\\)\\)\\>"
     . font-lock-builtin-face)
    )
  )

(defconst extensibella-output
  '(
    ;;Good proof done
    ("Proof completed."
     ;;There doesn't appear to be any default "success" face, but I'd
     ;;like this to stand out anyway.
     . font-lock-string-face)
    ;;Bad proof done
    ("Proof ABORTED."
     . font-lock-warning-face)
    ;;Errors in the output
    ;; Error: | Syntax error. | Search failed | Warning:
    ("\\<\\(\\(Error:\\)\\|\\(Syntax error.\\)\\|\\(Search failed\\)\\|\\(Warning:\\)\\)\\>"
     . font-lock-warning-face)
    ;;Highlight debug output demarcation to separate it from the actual output
    ("~+ .+ ~+"
     . font-lock-comment-face)
    ("\\*+ Abella Output \\*+"
     . font-lock-type-face)
    ("<<< No Commands >>>"
     . font-lock-warning-face)
    )
  )

(defconst extensibella-proof-state
  '(
    ;; Variables:
    ("Variables:"
     . font-lock-keyword-face)
    ;; Subgoal | is: | other subgoals | other subgoal
    ("\\<\\(\\(Subgoal\\)\\|\\(is:\\)\\|\\(other subgoals\\)\\|\\(other subgoal\\)\\)\\>"
     . font-lock-keyword-face)
    ;; Theorem
    ("Theorem"
     . font-lock-keyword-face)
    ("^[a-zA-Z0-9^=`'?$-_]+ : "
     . font-lock-type-face)
    )
  )




(defconst extensibella-script-font-lock-keywords
  (append extensibella-proof-commands
          extensibella-top-commands
          extensibella-common-commands
          extensibella-logic
          extensibella-comments
          )
  )

(defconst extensibella-goals-font-lock-keywords
  (append extensibella-logic
          extensibella-proof-state
          )
  )

(defconst extensibella-response-font-lock-keywords
  (append extensibella-logic
          extensibella-output
          extensibella-proof-state
          )
  )


;;Same as Abella's table
(defconst extensibella-mode-syntax-table-entries
  (append '(?_ "w")
          '(?' "w")
          '(?% "< b")
          '(?\n "> b")
          '(?/ ". 14n")
          '(?* ". 23n")
          '(?. ".")
          '(?+ ".")
          '(?= ".")
          '(?- ".")
          '(?> ".")
          '(?< ".")
          '(?# ".")
          '(?\ ".")
          '(?\" "\"")
          )
  )

