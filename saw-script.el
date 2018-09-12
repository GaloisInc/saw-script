;;; saw-script.el --- A major mode for editing SAW script files  -*- lexical-binding: t; -*-

;; Copyright (C) 2018  Galois, Inc

;; Author: David Thrane Christiansen <dtc@dtc.galois.com>
;; Keywords: languages
;; Package-Requires: ((emacs "24") (prop-menu "0.1") (cl-lib "0.5"))

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
(require 'cl-lib)
(require 'prop-menu)

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
    "include"
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
    (let ((compilation-finish-functions (list (lambda (x) (message "Done!")))))
      (compile command))))

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
    (define-key map (kbd "<mouse-3>") 'prop-menu-show-menu)
    (define-key map (kbd "C-c C-SPC") 'prop-menu-by-completing-read)
    map)
  "Keymap for SAWScript mode.")

;;; Output tracking
(defvar saw-script-output '() "The current output from SAWScript.")
(make-variable-buffer-local 'saw-script-output)

(defun saw-script-output-overlay-p (overlay)
  "Determine whether OVERLAY is describing SAWScript output."
  (and (overlayp overlay)
       (overlay-get overlay 'saw-script-output)))

(defun saw-script-clear-output ()
  "Clear the SAWScript output for the current buffer."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (dolist (o (overlays-in (point-min) (point-max)))
        (when (saw-script-output-overlay-p o)
          (delete-overlay o))))))

(defun saw-script-record-output (start-line start-column end-line end-column output)
  "Save SAWScript OUTPUT in the region delimited by START-LINE, START-COLUMN, END-LINE, END-COLUMN."
  (save-excursion
    (save-restriction
      (widen)
      (let ((start (progn (goto-char (point-min))
                          (forward-line (1- start-line))
                          (forward-char (1- start-column))
                          (point)))
            (end (progn (goto-char (point-min))
                        (forward-line (1- end-line))
                        (forward-char (1- end-column))
                        (point))))
        (let ((overlay (make-overlay start end)))
          (overlay-put overlay 'saw-script-output output)
          (overlay-put overlay 'face 'underline))))))

(defun saw-script--context-menu-items (plist)
  "Compute context menu items for PLIST."
  (let ((output (plist-get plist 'saw-script-output)))
    (if output
        (list (list "Show Output"
                    (let ((loc (point)))
                      (lambda ()
                        (interactive)
                        (saw-script-view-output loc)))))
      (list))))

(defun saw-script-output-buffer-name (file)
  "Find the name for output from FILE."
  (format "*SAW Output[%s]*" file))

(defun saw-script--view-overlay-output (overlay)
  "View the SAWScript output in OVERLAY."
  (let ((output (overlay-get overlay 'saw-script-output))
        (buffer (get-buffer-create (saw-script-output-buffer-name (buffer-file-name)))))
    (with-current-buffer buffer
      (read-only-mode 1)
      (let ((inhibit-read-only t))
        (widen)
        (erase-buffer)
        (insert output)
        (goto-char (point-min)))
      (pop-to-buffer buffer))))


(defun saw-script-view-output (pos)
  "View the SAWScript output at POS, if any."
  (interactive "d")
  (let ((tag (cl-gensym)))
    (let ((o (catch tag
               (progn (dolist (o (overlays-at pos))
                        (when (saw-script-output-overlay-p o)
                          (throw tag o)))
                      (error "No output at position %s" pos)))))
      (saw-script--view-overlay-output o))))

;;; Flycheck support

(defconst saw-script--output-regexp
  (rx (seq line-start "[output] at "
           (group-n 1 (1+ (not (any ?\:))))
           ":" (group-n 2 (1+ digit)) ":" (group-n 3 (1+ digit))
           "-" (group-n 5 (1+ digit)) ":" (group-n 6 (1+ digit)) ":" (0+ space)))
  "Output from SAWScript matches this regexp.")

(defconst saw-script--info-start-regexp
  (rx-to-string
   `(or (regexp ,saw-script--output-regexp)
        (seq line-start "[error] at "
             (group-n 1 (1+ (not (any ?\:))))
             ":" (group-n 2 (1+ digit)) ":" (group-n 3 (1+ digit))
             "--" (group-n 5 (1+ digit)) ":" (group-n 6 (1+ digit)) ":"
             (group-n 4 (1+ (seq "\n " (1+ (not (any ?\n)))))))
        (seq line-start "[warning] at "
             (group-n 1 (1+ (not (any ?\:))))
             ":" (group-n 2 (1+ digit)) ":" (group-n 3 (1+ digit))
             "--" (group-n 5 (1+ digit)) ":" (group-n 6 (1+ digit)) ":"
             (group-n 4 (1+ (seq "\n " (1+ (not (any ?\n)))))))
        (seq line-start "Parse error at " (group-n 1 (1+ (not (any ?\:))))
             ":" (group-n 2 (1+ digit)) ":" (group-n 3 (1+ digit))
             "-" (group-n 5 (1+ digit)) ":" (group-n 6 (1+ digit)) ":"
             (group-n 4 (1+ (not (any ?\n))))))))

(defun saw-script--abbreviate-string (str)
  "Cut off STR if it's too long."
  (if (> (length str) 120)
      (concat (substring str 0 117) "...")
    str))

(defun saw-script--flycheck-parse (output checker buffer)
  "Find Flycheck info in the string OUTPUT from saw using CHECKER applied to BUFFER."
  (with-current-buffer buffer (saw-script-clear-output))
  (save-excursion
    (save-match-data
      (let ((found '()))
        (with-temp-buffer
          (insert output)
          (goto-char (point-min))
          (while (re-search-forward saw-script--info-start-regexp nil t)
            (let ((filename (match-string 1))
                  (line (string-to-number (match-string 2)))
                  (column (string-to-number (match-string 3)))
                  (end-line (and (match-string 5)
                                 (string-to-number (match-string 5))))
                  (end-column (and (match-string 6)
                                   (string-to-number (match-string 6))))
                  (text (let ((perhaps-text (match-string 4)))
                          (or perhaps-text
                              (let ((text-start (point)))
                                (forward-line 1)
                                (beginning-of-line)
                                (while (and (not (eobp))
                                            (looking-at-p "\t"))
                                  (forward-line 1)
                                  (beginning-of-line))
                                (buffer-substring-no-properties text-start (point)))))))
              (push (flycheck-error-new-at line column
                                           (if (match-string 4) 'error 'info)
                                           (saw-script--abbreviate-string text)
                                           :checker checker :buffer buffer)
                    found)
              (unless (match-string 4)
                (with-current-buffer buffer
                  (saw-script-record-output line
                                            column
                                            end-line
                                            end-column
                                            text))))))
        found))))

(with-eval-after-load 'flycheck
  (flycheck-define-checker saw-script
    "A checker for SAWScript.

See URL `http://saw.galois.com' for more information."
    :command ("saw" "--output-locations" source-inplace)
    :error-parser saw-script--flycheck-parse
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

  ;; Comment syntax
  (setq-local comment-start "// ")
  (setq-local comment-end "")

  ;; Setup code for output viewing
  (make-variable-buffer-local 'saw-script-output)

  ;; Right click
  (set (make-local-variable 'prop-menu-item-functions) '(saw-script--context-menu-items))

  ;; Use Flycheck when possible
  (when (fboundp 'flycheck-mode)
    (when (boundp 'flycheck-checker)
      (setq flycheck-checker 'saw-script))
    (flycheck-mode 1)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.saw$" . saw-script-mode))


(provide 'saw-script)
;;; saw-script.el ends here
