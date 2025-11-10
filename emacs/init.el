;;; init.el --- Fil-C Emacs entrypoint -*- lexical-binding: t; -*-

(defconst filc/config-root
  (file-name-as-directory
   (if load-file-name
       (file-name-directory load-file-name)
     default-directory))
  "Root directory of the Fil-C Emacs configuration bundle.")

(add-to-list 'load-path (expand-file-name "lisp" filc/config-root))

(load-theme 'modus-vivendi t)

(require 'filc-paths)
(require 'filc-basics)
(require 'filc-completion)
(require 'filc-langs)
(require 'filc-eglot)

(when (file-exists-p custom-file)
  (load custom-file 'no-error 'nomessage))

(provide 'filc-init)
;;; init.el ends here

