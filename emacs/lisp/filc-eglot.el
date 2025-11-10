;;; filc-eglot.el --- Project-aware Eglot defaults -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

(require 'cl-lib)

(defgroup filc-eglot nil
  "Opinionated helpers for developing Fil-C projects with Eglot."
  :group 'filc)

(defun filc/eglot--executable (&rest candidates)
  "Return the first executable found among CANDIDATES."
  (cl-some #'executable-find candidates))

(use-package eglot
  :ensure nil
  :hook ((c-mode c-ts-mode c++-mode c++-ts-mode
          cmake-mode cmake-ts-mode
          meson-mode
          nix-mode
          llvm-mode tablegen-mode)
         . eglot-ensure)
  :custom
  (eglot-autoshutdown t)
  (eglot-report-progress nil)
  (eglot-confirm-server-initiated-edits nil)
  (eglot-events-buffer-size 0)
  :config
  ;; Keep the mode-line leaner but still expose the keymap prefix.
  (define-key eglot-mode-map (kbd "C-c l") eglot-command-map)
  (let ((clangd (or (filc/eglot--executable "clangd") "clangd")))
    (cl-pushnew
     `((c-mode c++-mode c-ts-mode c++-ts-mode)
       ,clangd
       "--header-insertion=never"
       "--clang-tidy"
       "--log=error")
     eglot-server-programs :test #'equal))
  (when-let ((nix-server (filc/eglot--executable "nixd" "nil")))
    (cl-pushnew
     `((nix-mode) ,nix-server)
     eglot-server-programs :test #'equal))
  (when-let ((cmake-server (filc/eglot--executable "cmake-language-server" "neocmakelsp")))
    (cl-pushnew
     `((cmake-mode cmake-ts-mode) ,cmake-server)
     eglot-server-programs :test #'equal))
  (when-let ((meson-server (filc/eglot--executable "mesonlsp")))
    (cl-pushnew
     `((meson-mode) ,meson-server)
     eglot-server-programs :test #'equal))
  (when-let ((llvm-server (filc/eglot--executable "mlir-lsp-server" "clangd")))
    (cl-pushnew
     `((llvm-mode tablegen-mode) ,llvm-server)
     eglot-server-programs :test #'equal)))

(use-package project
  :ensure nil
  :preface
  (defvar filc/eglot-build-dir-names '("build" "builds" "builddir" "out" ".filc-build")
    "Directory names searched (breadth-first) for a build tree.")

  (defun filc/eglot--project-build-dir (project)
    "Locate a build directory for PROJECT if one exists."
    (let* ((root (project-root project))
           (queue (list root))
           (seen (list root))
           match)
      (while (and queue (not match))
        (let ((dir (pop queue)))
          (when (file-exists-p (expand-file-name "compile_commands.json" dir))
            (setq match dir))
          (dolist (candidate filc/eglot-build-dir-names)
            (let ((path (expand-file-name candidate dir)))
              (when (and (file-directory-p path) (not (member path seen)))
                (push path seen)
                (push path queue)
                (when (file-exists-p (expand-file-name "compile_commands.json" path))
                  (setq match path))))))
        ;; Shallow search is fine; bail after first match.
        )
      match))

  (defun filc/eglot-derive-compile-command ()
    "Configure `compile-command' for the current project when appropriate."
    (when-let* ((project (project-current nil))
                (build-dir (filc/eglot--project-build-dir project)))
      (setq-local compile-command
                  (format "ninja -C %s" (shell-quote-argument build-dir)))))
  :hook
  ((c-mode c-ts-mode c++-mode c++-ts-mode) . filc/eglot-derive-compile-command))

(provide 'filc-eglot)
;;; filc-eglot.el ends here

