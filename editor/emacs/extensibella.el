
(require 'proof)
(require 'proof-easy-config)
(require 'extensibella-syntax)


(define-derived-mode extensibella-shell-mode proof-shell-mode
   "Extensibella shell" nil
   (extensibella-shell-config)
   (proof-shell-config-done))

(define-derived-mode extensibella-proof-mode proof-mode
   "Extensibella proof" nil
   (extensibella-proof-config)
   (proof-config-done))

(define-derived-mode extensibella-response-mode proof-response-mode
   "Extensibella response" nil
   (extensibella-response-config)
   (proof-response-config-done))

(define-derived-mode extensibella-goals-mode proof-goals-mode
   "Extensibella goals" nil
   (extensibella-goals-config)
   (proof-goals-config-done))


(proof-easy-config
 'extensibella "Extensibella"
 proof-assistant-home-page  "https://github.com/RandomActsOfGrammar/extensibella"

 proof-prog-name  "extensibella"

 proof-context-command                proof-no-regexp
 proof-showproof-command              "Show $$current."
 proof-find-theorems-command          "Show %s."
 proof-save-command-regexp            proof-no-regexp

 ;;Commands end with (period-space) or (period-EOF) or (period-close paren)
 proof-script-command-end-regexp    "\\.\\([ \n\t\r)]\\|$\\)"
 proof-script-comment-start-regexp  "%"
 proof-script-fly-past-comments     t
 proof-script-comment-end           "\n"
 proof-shell-strip-crs-from-input   nil

 proof-undo-n-times-cmd           'extensibella-undo-n
 proof-non-undoables-regexp       "\\(#back\\)\\|\\(#reset\\)\\|\\(undo\\)"
 proof-ignore-for-undo-count      ""
 proof-no-fully-processed-buffer  t
 proof-find-and-forget-fn         'extensibella-find-and-forget-fn

 proof-shell-restart-cmd   "#reset."
 proof-shell-quit-command  "Quit."

 proof-shell-annotated-prompt-regexp  "^.*< $"
 ;;error message regexp taken from Abella PG mode (https://github.com/abella-prover/PG)
 proof-shell-error-regexp            "Error:.*\\|\\(Syntax\\|Typing\\|Unification\\|Unknown\\) \\(e\\|E\\)rror\."
 proof-shell-proof-completed-regexp  "Proof completed."

 pg-top-term-regexp  "[a-zA-Z0-9^=`'?$-_]+ : "

 proof-script-font-lock-keywords      extensibella-script-font-lock-keywords
 proof-goals-font-lock-keywords       extensibella-goals-font-lock-keywords
 proof-response-font-lock-keywords    extensibella-response-font-lock-keywords
 proof-script-syntax-table-entries    extensibella-mode-syntax-table-entries
 proof-response-syntax-table-entries  extensibella-mode-syntax-table-entries
 proof-goals-syntax-table-entries     extensibella-mode-syntax-table-entries
)

(provide 'extensibella)


;;generate n commands to move back in the proof
(defun extensibella-undo-n (n)
  (if (= n 0)
      nil
    ("#back." . (extensibella-undo-n (- n 1)))
    )
  )


;;These three functions are taken from the Abella PG mode (https://github.com/abella-prover/PG).
;;The names are changed to be appropriate for this PG instance.
(defun extensibella-count (span)
  (setq next (next-span span 'name))
  (if (eq next nil)
    1
    (+ 1 (extensibella-count next))))

(defun extensibella-find-and-forget-cmd (span)
  (setq cmd (span-property span 'cmd))
  (cond
    ((eq cmd nil) "") ; comment
    (t " #back."))
  )

(defun extensibella-find-and-forget-fn (span)
  (setq ans ())
  (while span
    (setq typ (span-property span 'type))
    (if (not (eq typ 'comment))
      (let ((current-cmd (extensibella-find-and-forget-cmd span)))
        (setq ans (cons current-cmd ans))))
    (setq span (next-span span 'type)))
  ans)



;;This is probably not the best way to make it stop messing with the indentation.
;;However, it is the only one which has worked.
;;This makes it start a new line with the same indentation as the previous line
;;   and not change indentation on new line.
(add-hook 'extensibella-mode-hook
          (lambda ()
            (setq-local indent-line-function #'indent-relative)))

