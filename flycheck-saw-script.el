;;; flycheck-saw-script.el --- Flycheck mode for SAW script mode -*- lexical-binding: t; -*-

;; Copyright (C) 2018  Galois, Inc

;; Author: David Thrane Christiansen <dtc@dtc.galois.com>
;; Keywords: languages
;; Package-Requires: ((emacs "24.4") (prop-menu "0.1") (cl-lib "0.5") (flycheck "30") (saw-script "0.5"))
;; Package-Version: 0.5
;; Homepage: https://github.com/GaloisInc/saw-script

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

;;; This is a Flycheck mode to go in pair with SAWScript mode.

;;; Code:

(require 'flycheck)
(require 'saw-script)

(defconst flycheck-saw-script--output-regexp
  (rx (seq line-start "[output] at "
           (group-n 1 (1+ (not (any ?\:))))
           ":" (group-n 2 (1+ digit)) ":" (group-n 3 (1+ digit))
           "-" (group-n 5 (1+ digit)) ":" (group-n 6 (1+ digit)) ":" (0+ space)))
  "Output from SAWScript matches this regexp.")

(defconst flycheck-saw-script--info-start-regexp
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

(defun flycheck-saw-script--abbreviate-string (str)
  "Cut off STR if it's too long."
  (if (> (length str) 120)
      (concat (substring str 0 117) "...")
    str))

(flycheck-define-checker saw-script
  "A checker for SAWScript.

See URL `http://saw.galois.com' for more information."
  :command ("saw" "--output-locations" source-inplace)
  :error-parser flycheck-saw-script--flycheck-parse
  :modes (saw-script-mode))
(add-to-list 'flycheck-checkers 'saw-script)

(defun flycheck-saw-script--flycheck-parse (output checker buffer)
  "Find Flycheck info in the string OUTPUT from saw using CHECKER applied to BUFFER."
  (with-current-buffer buffer (saw-script-clear-output))
  (save-excursion
    (save-match-data
      (let ((found '()))
        (with-temp-buffer
          (insert output)
          (goto-char (point-min))
          (while (re-search-forward saw-script--info-start-regexp nil t)
            (let ((line (string-to-number (match-string 2)))
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
                                           (flycheck-saw-script--abbreviate-string text)
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


(provide 'flycheck-saw-script)
;;; flycheck-saw-script.el ends here
