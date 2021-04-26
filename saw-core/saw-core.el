;;; saw-core.el --- A major mode for editing saw-core  -*- lexical-binding: t; -*-

;; Copyright (C) 2020 Galois, Inc

;; Author: David Thrane Christiansen <dtc@000301-dtc>
;; Keywords: languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing saw-core's concrete syntax.

;;; Code:

(require 'compile)
(require 'flycheck)

;;; Config

(defgroup saw-core '()
  "saw-core"
  :group 'languages
  :tag "saw-core")

(defcustom saw-core-saw-script-command "saw"
  "The command to run to execute saw."
  :type 'string
  :group 'saw-core)

(defface saw-core-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "How to highlight saw-core keywords."
  :group 'saw-core)

(defface saw-core-builtin-face
  '((t (:inherit font-lock-builtin-face)))
  "How to highlight saw-core built-in syntax."
  :group 'saw-core)

(defface saw-core-eliminator-face
  '((t (:inherit font-lock-string-face)))
  "How to highlight saw-core eliminators."
  :group 'saw-core)

(defface saw-core-punctuation-face
  '((t (:inherit font-lock-constant-face)))
  "How to highlight saw-core punctuation elements."
  :group 'saw-core)


;;; Syntax table

(defvar saw-core-mode-syntax-table
  (let ((syntax-table (make-syntax-table)))
    ;; Set up -- line comments and {- ... -} block comments
    (modify-syntax-entry ?\- ". 123" syntax-table)
    (modify-syntax-entry ?\{ "(} 1bn" syntax-table)
    (modify-syntax-entry ?\} "){ 4bn" syntax-table)
    (modify-syntax-entry ?\n ">" syntax-table)

    syntax-table)
  "Syntax table for `saw-core-mode'.")

;;; font-lock

(defconst saw-core-keywords
  (list "axiom" "module" "import" "where" "data" "sort" "primitive")
  "Keywords to highlight in saw-core buffers.")

(defconst saw-core--keyword-regexp
  (regexp-opt saw-core-keywords 'words)
  "Regular expression that matches saw-core keywords for highlighting.")

(defconst saw-core-punctuation
  (list ":" "(" ")" "{" "}" ";" "=" ",")
  "Punctuation to highlight in saw-core buffers.")

(defconst saw-core--punctuation-regexp
  (regexp-opt saw-core-punctuation)
  "Regular expression that matches saw-core keywords for highlighting.")

(defconst saw-core-font-lock-defaults
  `(( (,saw-core--keyword-regexp . 'saw-core-keyword-face)
      (,saw-core--punctuation-regexp . 'saw-core-punctuation-face)
      ("\\<[a-zA-Z]+#rec\\>" . 'saw-core-eliminator-face)
      ;; Language elements named by syntax rather than by an identifier
      ("#" . 'saw-core-builtin-face)
      ("\\(\\\\\\)[^\\]" . (0 'saw-core-builtin-face))
      ("->" . 'saw-core-builtin-face)
      ("*" . 'saw-core-builtin-face)
      ("\\.([0-9]+)" . 'saw-core-builtin-face)
      )
    nil nil nil nil)
  "Highlighting instructions for saw-core.")

;;; imenu support for navigation

(defconst saw-core-imenu-generic-expression
  (list
   `(nil "\\<data\\ \\([a-zA-Z_][a-zA-Z0-9_]+\\)" 1)
   `(nil "\\<primitive\\> +\\([a-zA-Z_][a-zA-Z0-9_]+\\)" 1)
   `(nil "\\<axiom\\> +\\([a-zA-Z_][a-zA-Z0-9_]+\\)" 1)
   `(nil "^\\([a-zA-Z_][a-zA-Z0-9_]+\\) *:" 1)))

;;; The mode itself
(define-derived-mode saw-core-mode prog-mode "saw-core"
  "A major mode for editing saw-core files."
  :syntax-table saw-core-mode-syntax-table
  (setq font-lock-defaults saw-core-font-lock-defaults)
  (setq font-lock-multiline t)

  ;; Comment syntax
  (setq-local comment-start "-- ")
  (setq-local comment-end "")

  ;; imenu
  (setq-local imenu-generic-expression saw-core-imenu-generic-expression)

  ;; Indentation
  (setq-local indent-line-function 'indent-relative))

(add-to-list 'auto-mode-alist '("\\.sawcore\\'" . saw-core-mode))

(provide 'saw-core)
;;; saw-core.el ends here
