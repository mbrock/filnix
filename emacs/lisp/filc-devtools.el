;;; filc-devtools.el --- Fil-C helper modes -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

;; which-key - Show available keybindings in popup
(use-package which-key
  :ensure nil
  :demand t
  :config
  (which-key-mode 1)
  :custom
  (which-key-idle-delay 0.5)
  (which-key-popup-type 'minibuffer)
  (which-key-sort-order 'which-key-prefix-then-key-order))

;; diff-hl - Show git diff in fringe
(use-package diff-hl
  :ensure nil
  :demand t
  :config
  (global-diff-hl-mode 1)
  :hook
  ((magit-pre-refresh . diff-hl-magit-pre-refresh)
   (magit-post-refresh . diff-hl-magit-post-refresh)))

;; rainbow-delimiters - Colorful nested delimiters
(use-package rainbow-delimiters
  :ensure nil
  :hook
  ((prog-mode . rainbow-delimiters-mode)))

;; envrc - direnv integration for Nix flakes
(use-package envrc
  :ensure nil
  :config
  (envrc-global-mode 1))

(provide 'filc-devtools)
;;; filc-devtools.el ends here

