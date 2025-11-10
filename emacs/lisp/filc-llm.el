;;; filc-llm.el --- Optional LLM helpers -*- lexical-binding: t; -*-

(defun filc/llm-expand ()
  "Expand the surrounding context using a Fil-C aware LLM workflow.

This is a placeholder meant to be replaced with a real integration.
Bind it or advise it to call out to your preferred tooling."
  (interactive)
  (user-error "Hook up `filc/llm-expand' to the Fil-C LLM backend of your choice."))

(global-set-key (kbd "C-c e") #'filc/llm-expand)

(provide 'filc-llm)
;;; filc-llm.el ends here

