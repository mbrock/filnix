;;; filc-devtools.el --- Fil-C helper modes -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

(use-package envrc
  :ensure nil
  :init
  (envrc-global-mode 1))

(defface filc/hole-face
  '((t :inherit font-lock-warning-face :weight bold))
  "Face used to highlight Fil-C style hole placeholders."
  :group 'filc)

(defconst filc/hole--regexp ":<[[:alnum:]-_]+>"
  "Regexp that matches Fil-C placeholder holes.")

(defvar filc/hole--keywords
  `((,filc/hole--regexp 0 'filc/hole-face prepend))
  "Font-lock keywords used by `filc/hole-mode'.")

(define-minor-mode filc/hole-mode
  "Highlight Fil-C placeholders shaped like :<foo>."
  :lighter " :<>"
  (if filc/hole-mode
      (progn
        (font-lock-add-keywords nil filc/hole--keywords 'append)
        (font-lock-flush)
        (font-lock-ensure))
    (font-lock-remove-keywords nil filc/hole--keywords)
    (font-lock-flush)))

(add-hook 'prog-mode-hook #'filc/hole-mode)

(provide 'filc-devtools)
;;; filc-devtools.el ends here

