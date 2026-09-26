;;; Parse C with a Fil-C tree-sitter grammar and query it with predicates.

(require 'treesit)

(unless (treesit-language-available-p 'c)
  (error "C grammar unavailable: %S" (treesit-language-available-p 'c t)))

(with-temp-buffer
  (insert "int answer(void) { return 42; }\nint main(void) { return answer(); }\n")
  (let* ((root (treesit-parser-root-node (treesit-parser-create 'c)))
         ;; tree-sitter 0.26 only accepts the #eq?/#match? spellings.
         (calls (treesit-query-capture
                 root '((call_expression
                         function: (identifier) @callee
                         (:equal @callee "answer")))))
         (numbers (treesit-query-capture
                   root '(((number_literal) @n (:match "\\`4[0-9]\\'" @n))))))
    (princ (format "root=%s calls=%S numbers=%S\n"
                   (treesit-node-type root)
                   (mapcar (lambda (c) (treesit-node-text (cdr c))) calls)
                   (mapcar (lambda (c) (treesit-node-text (cdr c))) numbers)))
    (unless (and (equal (treesit-node-type root) "translation_unit")
                 (equal (mapcar (lambda (c) (treesit-node-text (cdr c))) calls)
                        '("answer"))
                 (equal (mapcar (lambda (c) (treesit-node-text (cdr c))) numbers)
                        '("42")))
      (error "unexpected tree-sitter results"))))
