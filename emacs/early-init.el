;;; early-init.el --- Fil-C Emacs early setup -*- lexical-binding: t; -*-

;; Avoid loading the package manager twice; `init.el` handles initialization.
(setq package-enable-at-startup nil)

;; Make frame resizing behave sensibly when running under a terminal multiplexer.
(setq frame-resize-pixelwise t)

(provide 'filc-early-init)
;;; early-init.el ends here

