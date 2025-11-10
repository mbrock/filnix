;;; filc-org.el --- Org-mode configuration -*- lexical-binding: t; -*-

(eval-when-compile
  (require 'use-package))

(require 'filc-paths)

(defconst filc/org-notes-file
  (or (getenv "FILC_EMACS_INDEX")
      (expand-file-name "index.org" (or (getenv "HOME") default-directory)))
  "Default location for Org capture notes.")

(make-directory (file-name-directory filc/org-notes-file) t)

(use-package org
  :ensure nil
  :bind (("C-c n" . org-capture))
  :config
  (setq org-default-notes-file filc/org-notes-file
        org-capture-templates
        '(("n" "Note" entry
           (file+datetree filc/org-notes-file)
           "* %U :<title>\n  %i\n  %a")))

  (use-package ob
    :ensure nil
    :config
    (org-babel-do-load-languages
     'org-babel-load-languages
     '((shell . t)
       (emacs-lisp . t)
       (sql . t))))

  (with-eval-after-load 'ox
    (add-to-list 'org-export-backends 'texinfo)))

(autoload 'org-texinfo-export-to-info "ox-texinfo")

(defun filc/export-emacs-org-to-info ()
  "Export the bundled emacs.org to Texinfo INFO format."
  (interactive)
  (require 'org)
  (require 'ox-texinfo)
  (find-file (expand-file-name "emacs.org" filc/config-root))
  (org-texinfo-export-to-info))

(defun filc/export-index-org-to-info ()
  "Export the user's index.org notes file to Texinfo INFO format."
  (interactive)
  (require 'org)
  (require 'ox-texinfo)
  (find-file filc/org-notes-file)
  (org-texinfo-export-to-info))

(provide 'filc-org)
;;; filc-org.el ends here

