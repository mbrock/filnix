;;; filc-basics.el --- Core Fil-C configuration -*- lexical-binding: t; -*-

(require 'filc-paths)

(setq inhibit-startup-screen t
      inhibit-startup-message t
      inhibit-startup-buffer-menu t
      initial-scratch-message nil
      ring-bell-function #'ignore
      confirm-kill-emacs #'y-or-n-p)

(when (fboundp 'tool-bar-mode)
  (tool-bar-mode -1))
(when (fboundp 'menu-bar-mode)
  (menu-bar-mode -1))
(when (fboundp 'scroll-bar-mode)
  (scroll-bar-mode -1))

(add-to-list 'default-frame-alist '(undecorated . t))

(setq-default indent-tabs-mode nil)

;; Display enhancements
(global-display-line-numbers-mode 0)
(global-hl-line-mode 0)
(show-paren-mode 1)
(setq show-paren-delay 0)

;; Better scrolling behavior
(setq scroll-margin 3
      scroll-conservatively 101
      scroll-preserve-screen-position t
      auto-window-vscroll nil)

;; Enable useful modes
(save-place-mode 1)
(recentf-mode 1)
(global-auto-revert-mode 1)
(delete-selection-mode 1)
(electric-pair-mode 1)
(column-number-mode 1)

;; Window navigation with Shift+arrows
(windmove-default-keybindings)

;; Compilation and version control
(global-set-key (kbd "C-x c") #'compile)
(global-set-key (kbd "C-x g") #'magit-status)
(global-set-key (kbd "C-c c") #'recompile)
(global-set-key (kbd "C-c j") #'join-line)

;; Project management
(global-set-key (kbd "C-x p p") #'project-switch-project)
(global-set-key (kbd "C-x p f") #'project-find-file)

(autoload 'magit-status "magit" nil t)
(autoload 'magit-dispatch "magit" nil t)
(autoload 'vterm "vterm" nil t)
(autoload 'vterm-other-window "vterm" nil t)

;; Fil-C branding and welcome message
(defun filc/show-welcome ()
  "Display welcome message highlighting Fil-C memory safety."
  (interactive)
  (message "You feel an uncanny sense of safety...  Welcome to Fil-C GNU Emacs."))

;; Show welcome message on first startup
(when (and (not (daemonp))
           (< (length command-line-args) 2))
  (add-hook 'emacs-startup-hook #'filc/show-welcome))

;; Add Fil-C indicator to mode line
(setq-default mode-line-misc-info
              (cons '(:eval
                      (propertize "  Fil-C"
                                  'face '(:foreground "goldenrod")
                                  'help-echo "Compiled with Fil-C for memory safety"))
                    mode-line-misc-info))

(provide 'filc-basics)
;;; filc-basics.el ends here

