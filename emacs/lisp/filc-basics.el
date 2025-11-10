;;; filc-basics.el --- Core Fil-C configuration -*- lexical-binding: t; -*-

(require 'filc-paths)

(setq inhibit-startup-screen t
      inhibit-startup-message t
      inhibit-startup-buffer-menu t
      initial-scratch-message nil
      ring-bell-function #'ignore
      confirm-kill-emacs #'y-or-n-p)

(tool-bar-mode -1)
(menu-bar-mode -1)
(when (fboundp 'scroll-bar-mode)
  (scroll-bar-mode -1))

(add-to-list 'default-frame-alist '(undecorated . t))

(setq-default indent-tabs-mode nil
              line-spacing 4)

(save-place-mode 1)
(recentf-mode 1)
(global-auto-revert-mode 1)
(delete-selection-mode 1)
(electric-pair-mode 1)
(column-number-mode 1)

(global-set-key (kbd "C-x c") #'compile)
(global-set-key (kbd "C-x g") #'magit-status)
(global-set-key (kbd "C-c c") #'recompile)
(global-set-key (kbd "C-c j") #'join-line)

(autoload 'magit-status "magit" nil t)
(autoload 'magit-dispatch "magit" nil t)
(autoload 'vterm "vterm" nil t)
(autoload 'vterm-other-window "vterm" nil t)

(provide 'filc-basics)
;;; filc-basics.el ends here

