;;; filc-completion.el --- Minibuffer & completion UX -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

(use-package vertico
  :ensure nil
  :init
  (vertico-mode 1)
  :custom
  (vertico-count 20)
  :bind
  (:map vertico-map
        ("<prior>" . vertico-scroll-down)
        ("<next>" . vertico-scroll-up)))

(use-package vertico-directory
  :ensure nil
  :after vertico
  :bind
  (:map vertico-map
        ("DEL" . vertico-directory-delete-char)
        ("M-DEL" . vertico-directory-delete-word)))

(use-package orderless
  :ensure nil
  :custom
  (completion-styles '(orderless basic))
  (completion-category-overrides '((file (styles partial-completion)))))

(use-package consult
  :ensure nil
  :custom
  (consult-preview-key nil)
  :bind
  (("C-x b" . consult-buffer)
   ("M-l" . consult-git-grep)
   ("M-y" . consult-yank-pop)
   ("M-s" . consult-line)))

(use-package embark
  :ensure nil
  :bind
  (("C-." . embark-act)
   ("C-;" . embark-dwim)
   ("C-h B" . embark-bindings))
  :init
  (setq prefix-help-command #'embark-prefix-help-command)
  :config
  (use-package embark-consult
    :ensure nil
    :hook (embark-collect-mode . consult-preview-at-point-mode)))

(use-package marginalia
  :ensure nil
  :bind
  (:map minibuffer-local-map
        ("M-a" . marginalia-cycle))
  :init
  (marginalia-mode 1))

(use-package savehist
  :ensure nil
  :init
  (savehist-mode 1))

(use-package emacs
  :ensure nil
  :custom
  (context-menu-mode t)
  (enable-recursive-minibuffers t)
  (read-extended-command-predicate #'command-completion-default-include-p)
  (minibuffer-prompt-properties '(read-only t cursor-intangible t face minibuffer-prompt))
  :hook
  (minibuffer-setup . cursor-intangible-mode))

(provide 'filc-completion)
;;; filc-completion.el ends here

