;;; init.el --- Fil-C Emacs entrypoint -*- lexical-binding: t; -*-

(defconst filc/config-root
  (file-name-as-directory
   (if load-file-name
       (file-name-directory load-file-name)
     default-directory))
  "Root directory of the Fil-C Emacs configuration bundle.")

(add-to-list 'load-path (expand-file-name "lisp" filc/config-root))

(require 'filc-paths)
(require 'filc-basics)
(require 'filc-completion)
(require 'filc-langs)
(require 'filc-eglot)
(require 'filc-devtools)

;; Optional modules:
;; (require 'filc-org)
;; (require 'filc-llm)

(when (file-exists-p custom-file)
  (load custom-file 'no-error 'nomessage))

(provide 'filc-init)
;;; init.el ends here

