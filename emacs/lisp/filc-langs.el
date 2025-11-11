;;; filc-langs.el --- Language-centric helpers -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

(use-package paredit
  :ensure nil
  :hook ((emacs-lisp-mode . enable-paredit-mode)
         (lisp-mode . enable-paredit-mode)
         (lisp-interaction-mode . enable-paredit-mode)
         (ielm-mode . enable-paredit-mode)
         (scheme-mode . enable-paredit-mode)
         (sly-mode . enable-paredit-mode)
         (sly-repl-mode . enable-paredit-mode)))

(use-package meson-mode
  :ensure nil
  :mode (("meson\\.build\\'" . meson-mode)
         ("meson_options\\.txt\\'" . meson-mode)))

(use-package nix-mode
  :ensure nil)

(provide 'filc-langs)
;;; filc-langs.el ends here

