;;; saw-script.el --- A major mode for editing SAW script files  -*- lexical-binding: t; -*-

;; Copyright (C) 2018  Galois, Inc

;; Author: David Thrane Christiansen <dtc@dtc.galois.com>
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
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing SAWScript files.

;;; Code:

(require 'compile)

;;; Configuration

(defgroup saw-script '()
  "SAWScript"
  :group 'languages
  :tag "SAWScript")

(defcustom saw-script-command "saw"
  "The command to run to execute saw."
  :type 'string
  :group 'saw-script)

(defface saw-script-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "How to highlight SAWScript keywords."
  :group 'saw-script)

(defface saw-script-operator-face
  '((t (:inherit font-lock-keyword-face)))
  "How to highlight SAWScript build-in operators."
  :group 'saw-script)

(defface saw-script-embedded-cryptol-brace-face
  '((t (:inherit font-lock-preprocessor-face)))
  "How to highlight the braces around embedded Cryptol in SAWScript."
  :group 'saw-script)

(defface saw-script-embedded-cryptol-face
  '((t (:inherit font-lock-builtin-face)))
  "How to highlight embedded Cryptol in SAWScript."
  :group 'saw-script)

(defface saw-script-embedded-cryptol-type-brace-face
  '((t (:inherit font-lock-reference-face)))
  "How to highlight the braces around embedded Cryptol types in SAWScript."
  :group 'saw-script)

(defface saw-script-embedded-cryptol-type-face
  '((t (:inherit font-lock-builtin-face)))
  "How to highlight embedded Cryptol types in SAWScript."
  :group 'saw-script)


;;; Syntax table

(defvar saw-script-mode-syntax-table
  (let ((syntax-table (make-syntax-table)))
    ;; Set up // line comments and /* */ block comments
    (modify-syntax-entry ?/ ". 124" syntax-table)
    (modify-syntax-entry ?* ". 23bn" syntax-table)
    (modify-syntax-entry ?\n ">" syntax-table)

    syntax-table)
  "Syntax table for `saw-script-mode'.")

;;; Highlighting

(defconst saw-script-keywords
  '("import"
    "and"
    "as"
    "hiding"
    "let"
    "rec"
    "in"
    "do"
    "if"
    "then"
    "else"))

(defvar saw-script--keyword-regexp
  (regexp-opt saw-script-keywords 'words)
  "Regular expression for SAWScript keyword highlighting.")

(defconst saw-script-operators
  '("<-" "=" "==")
  "Operators to highlight in SAWScript.")

(defvar saw-script--operator-regexp
  (regexp-opt saw-script-operators)
  "Regular expression for SAWScript keyword highlighting.")

(defun saw-script--add-multiline (end face)
  "Find the end of embedded Cryptol or type terminating with END, and add a text property for font-lock FACE."
  (save-match-data
    (save-excursion
      (let ((start (point)))
        (when (re-search-forward end nil t)
          (with-silent-modifications
            (put-text-property start (- (point) 2)
                               'face face)
            (put-text-property start (- (point) 2)
                               'fontified t)
            (put-text-property start (point)
                               'font-lock-multiline t)
            (put-text-property start (point)
                               'cryptol t)))
        (point)))))

(defun saw-script--extend-after-change-region-function (beg end _old-len)
  "Find embedded Cryptol for refontification in the region described by BEG, END, and OLD-LEN."
  (save-excursion
    (save-restriction
      (save-match-data
        (let ((beginning-is-cryptol (get-text-property beg 'cryptol))
              (end-is-cryptol  (get-text-property end 'cryptol)))
          (if (or beginning-is-cryptol end-is-cryptol)
              (cons
               (progn (goto-char beg)
                      (while (and (get-text-property (point) 'cryptol) (> (point) (point-min)))
                        (forward-char -1))
                      (point))
               (progn (goto-char end)
                      (while (and (get-text-property (point) 'cryptol) (> (point) (point-max)))
                        (forward-char 1))
                      (point)))
            nil))))))

(defvar saw-script-font-lock-defaults
  `((
     (,saw-script--keyword-regexp . 'saw-script-keyword-face)
     ("{{" (0 'saw-script-embedded-cryptol-brace-face)
      ("\\(.*\\)\\(}}\\)" (saw-script--add-multiline "}}" 'saw-script-embedded-cryptol-face) nil
       (1 'saw-script-embedded-cryptol-face)
       (2 'saw-script-embedded-cryptol-brace-face)))
     ("{|" (0 'saw-script-embedded-cryptol-type-brace-face)
      ("\\(.*\\)\\(|}\\)" (saw-script--add-multiline "|}" 'saw-script-embedded-cryptol-type-face) nil
       (1 'saw-script-embedded-cryptol-type-face)
       (2 'saw-script-embedded-cryptol-type-brace-face)))
     (,saw-script--operator-regexp . 'saw-script-operator-face)
     (";" . 'saw-script-operator-face)
     ("," . 'saw-script-operator-face)
     ("\\[" . 'saw-script-operator-face)
     ("\\]" . 'saw-script-operator-face)
     )
    nil nil nil
    (font-lock-extend-after-change-region-function . saw-script--extend-after-change-region-function))
  "Highlighting instructions for SAWScript.")


;;; Running SAWScript

(defun saw-script--compilation-buffer-name-function (_mode)
  "Compute a name for the SAW compilation buffer."
  "*SAW*")

(defun saw-script-run-file (filename)
  "Run FILENAME in saw."
  (interactive "fFile to run in saw: ")
  (let* ((dir (file-name-directory filename))
         (file (file-name-nondirectory filename))
         (command (concat saw-script-command " --output-locations " file))
         ;; Special variables that configure compilation mode
         (compilation-buffer-name-function
          'saw-script--compilation-buffer-name-function)
         (default-directory dir) )
    (compile command)))

(defun saw-script-run-buffer (buffer)
  "Run the file from BUFFER in saw."
  (interactive "bBuffer: ")
  (let ((file (buffer-file-name buffer)))
    (if file
        (progn (when (buffer-modified-p buffer)
                 (when (yes-or-no-p "Buffer modified. Save first? ")
                   (save-buffer buffer)))
               (saw-script-run-file file))
      (error "Buffer %s has no file" buffer))))

(defun saw-script-run-current-buffer ()
  "Run the current buffer in saw."
  (interactive)
  (saw-script-run-buffer (current-buffer)))

;;; Default keybindings

(defvar saw-script-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'saw-script-run-current-buffer)
    (define-key map (kbd "C-c C-l") 'saw-script-run-current-buffer)
    map)
  "Keymap for SAWScript mode.")

;;; Flycheck support
(with-eval-after-load 'flycheck
  (flycheck-define-checker saw-script
    "A checker for SAWScript.

See URL `http://saw.galois.com' for more information."
    :command ("saw" "--output-locations" source-inplace)
    :error-patterns ((info line-start "[output] at " (file-name (1+ (not (any ?\:)))) ":" line ":" column "-" (1+ digit) ":" (1+ digit) ": " (message))
                     (error line-start (file-name) ":" line ":" column "-" (1+ digit) ":" (1+ digit) ":"
                            (message) line-end)
                     (error (seq line-start "[error] at " (file-name (1+ (not (any ?\:)))) ":" line ":" column
                                 "--" (group (1+ digit)) ":" (group (1+ digit)) ":"
                                 (message (1+ (seq "\n " (1+ (not (any ?\n))))))))
                     (warning (seq line-start "[warning] at " (file-name (1+ (not (any ?\:)))) ":" line ":" column
                                   "--" (group (1+ digit)) ":" (group (1+ digit)) ":"
                                   (message (1+ (seq "\n " (1+ (not (any ?\n)))))))))
    :modes (saw-script-mode))
  (add-to-list 'flycheck-checkers 'saw-script))

;;; The mode itself

;;;###autoload
(define-derived-mode saw-script-mode prog-mode "SAWScript"
  "A major mode for editing SAWScript files."
  (setq font-lock-defaults saw-script-font-lock-defaults)
  (setq font-lock-multiline t)

  ;; Compilation mode highlighting
  (add-to-list 'compilation-error-regexp-alist-alist
               '(saw-script "$\\([^:]+\\):\\([0-9]+\\):\\(0-9\\)-\\([0-9]+\\):\\(0-9\\): "
                            1 (2 . 4) (3 . 5) nil 0))
  (add-to-list 'compilation-error-regexp-alist-alist
               '(cryptol-warning
                 "\\[warning\\] at \\([^:]+\\):\\([0-9]+\\):\\([0-9]+\\)--\\([0-9]+\\):\\([0-9+]\\)"
                 1 (2 . 4) (3 . 5) 1))
  (add-to-list 'compilation-error-regexp-alist-alist
               '(cryptol-error
                 "\\[error\\] at \\([^:]+\\):\\([0-9]+\\):\\([0-9]+\\)--\\([0-9]+\\):\\([0-9+]\\)"
                 1 (2 . 4) (3 . 5) 1))
  (add-to-list 'compilation-error-regexp-alist 'saw-script)
  (add-to-list 'compilation-error-regexp-alist 'cryptol-warning)
  (add-to-list 'compilation-error-regexp-alist 'cryptol-error)
  )

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.saw$" . saw-script-mode))


(provide 'saw-script)
;;; saw-script.el ends here
