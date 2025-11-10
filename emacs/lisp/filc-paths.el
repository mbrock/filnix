;;; filc-paths.el --- Fil-C path helpers -*- lexical-binding: t; -*-

(defgroup filc nil
  "Fil-C Emacs configuration."
  :group 'applications)

(defun filc/xdg-path (env xdg fallback-subdir)
  "Resolve ENV, XDG, or FALLBACK-SUBDIR under HOME to an absolute path."
  (let* ((home (or (getenv "HOME") default-directory))
         (env-value (getenv env))
         (xdg-value (getenv xdg)))
    (cond
     (env-value (expand-file-name env-value home))
     (xdg-value (expand-file-name fallback-subdir xdg-value))
     (t (expand-file-name fallback-subdir home)))))

(defconst filc/state-dir
  (file-name-as-directory
   (filc/xdg-path "FILC_EMACS_STATE_DIR" "XDG_STATE_HOME" ".local/state/filc-emacs"))
  "Writable directory for Fil-C Emacs state.")

(defconst filc/cache-dir
  (file-name-as-directory
   (filc/xdg-path "FILC_EMACS_CACHE_DIR" "XDG_CACHE_HOME" ".cache/filc-emacs"))
  "Writable directory for Fil-C Emacs cache files.")

(defconst filc/config-dir
  (file-name-as-directory
   (filc/xdg-path "FILC_EMACS_CONFIG_HOME" "XDG_CONFIG_HOME" ".config/filc-emacs"))
  "Writable directory for Fil-C Emacs user configuration.")

(dolist (dir (list filc/state-dir
                   filc/cache-dir
                   filc/config-dir
                   (expand-file-name "auto-save-list" filc/state-dir)
                   (expand-file-name "backups" filc/state-dir)
                   (expand-file-name "url" filc/state-dir)))
  (make-directory dir t))

(setq user-emacs-directory filc/state-dir
      package-user-dir (expand-file-name "elpa" filc/state-dir)
      custom-file (expand-file-name "custom.el" filc/config-dir)
      auto-save-list-file-prefix (expand-file-name "auto-save-list/.saves-" filc/state-dir)
      backup-directory-alist `(("." . ,(expand-file-name "backups" filc/state-dir)))
      url-history-file (expand-file-name "url/history" filc/state-dir)
      recentf-save-file (expand-file-name "recentf" filc/state-dir)
      bookmark-default-file (expand-file-name "bookmarks" filc/state-dir))

(provide 'filc-paths)
;;; filc-paths.el ends here

