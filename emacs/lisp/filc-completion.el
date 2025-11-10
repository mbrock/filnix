;;; filc-completion.el --- Minibuffer & completion UX -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

;; Core completion settings - set these first
(use-package emacs
  :ensure nil
  :init
  ;; Basic completion settings
  (setq completion-styles '(orderless basic)
        completion-category-defaults nil
        completion-category-overrides '((file (styles partial-completion)))
        completion-ignore-case t
        read-buffer-completion-ignore-case t
        read-file-name-completion-ignore-case t)

  ;; Minibuffer settings
  (setq enable-recursive-minibuffers t
        read-extended-command-predicate #'command-completion-default-include-p
        minibuffer-prompt-properties '(read-only t cursor-intangible t face minibuffer-prompt))

  ;; Context menu (works in TTY with xterm-mouse-mode if needed)
  (setq context-menu-mode t)

  :hook
  (minibuffer-setup . cursor-intangible-mode))

;; Orderless - flexible matching (must be loaded before vertico)
(use-package orderless
  :ensure nil
  :demand t)

;; Vertico - vertical completion UI
(use-package vertico
  :ensure nil
  :demand t
  :config
  (vertico-mode 1)
  :custom
  (vertico-count 20)
  (vertico-resize nil)
  (vertico-cycle t)
  :bind
  (:map vertico-map
        ("C-j" . vertico-next)
        ("C-k" . vertico-previous)
        ("<prior>" . vertico-scroll-down)
        ("<next>" . vertico-scroll-up)
        ("C-M-n" . vertico-next-group)
        ("C-M-p" . vertico-previous-group)))

;; Vertico directory navigation
(use-package vertico-directory
  :ensure nil
  :after vertico
  :bind
  (:map vertico-map
        ("RET" . vertico-directory-enter)
        ("DEL" . vertico-directory-delete-char)
        ("M-DEL" . vertico-directory-delete-word)))

;; Marginalia - rich annotations in minibuffer
(use-package marginalia
  :ensure nil
  :demand t
  :config
  (marginalia-mode 1)
  :bind
  (:map minibuffer-local-map
        ("M-a" . marginalia-cycle)))

;; Consult - enhanced commands with completion
(use-package consult
  :ensure nil
  :custom
  (consult-preview-key nil)
  :bind
  (("C-x b" . consult-buffer)
   ("C-x 4 b" . consult-buffer-other-window)
   ("M-y" . consult-yank-pop)
   ("M-s l" . consult-line)
   ("M-s L" . consult-line-multi)
   ("M-s g" . consult-grep)
   ("M-s G" . consult-git-grep)
   ("M-s r" . consult-ripgrep)
   ("M-g i" . consult-imenu)
   ("M-g I" . consult-imenu-multi)))

;; Embark - contextual actions
(use-package embark
  :ensure nil
  :bind
  (("C-." . embark-act)
   ("C-;" . embark-dwim)
   ("C-h B" . embark-bindings))
  :init
  (setq prefix-help-command #'embark-prefix-help-command))

;; Embark + Consult integration
(use-package embark-consult
  :ensure nil
  :after (embark consult)
  :hook
  (embark-collect-mode . consult-preview-at-point-mode))

;; Save minibuffer history
(use-package savehist
  :ensure nil
  :demand t
  :config
  (savehist-mode 1)
  :custom
  (history-length 10000)
  (history-delete-duplicates t)
  (savehist-save-minibuffer-history t))

;; Company - in-buffer completion (manual trigger only)
(use-package company
  :ensure nil
  :commands (company-mode company-complete)
  :init
  ;; Enable company in programming modes
  (add-hook 'prog-mode-hook #'company-mode)
  :custom
  ;; Manual completion only - no automatic popups
  (company-idle-delay nil)
  (company-minimum-prefix-length 2)
  (company-show-quick-access 'left)
  (company-selection-wrap-around t)
  (company-tooltip-align-annotations t)
  (company-require-match nil)
  (company-dabbrev-downcase nil)
  (company-dabbrev-ignore-case nil)
  :bind
  (:map company-mode-map
        ("C-c TAB" . company-complete)
        ("C-c <tab>" . company-complete))
  (:map company-active-map
        ("C-j" . company-select-next)
        ("C-k" . company-select-previous)
        ("C-n" . company-select-next)
        ("C-p" . company-select-previous)
        ("TAB" . company-complete-selection)
        ("<tab>" . company-complete-selection)
        ("RET" . nil)
        ("<return>" . nil)))

(provide 'filc-completion)
;;; filc-completion.el ends here

