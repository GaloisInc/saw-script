;;; inf-saw.el --- an inferior-saw mode
;;;
;;; Derived from inf-lisp that ships with Emacs; that file is GPL version 3
;;; so I suppose this file is also GPL.
;;;
;;; This allows a saw-script interpreter to be run as a subprocess
;;; with inputs and outputs in a buffer, typically *inferior-saw*.
;;; Besides the usual comint bindings for command-line history an so
;;; on, bindings are added to saw-script-mode-map that allow items
;;; from buffers in SawScript mode to be sent to the saw process.
;;;

(require 'comint)
(require 'saw-script)

(defgroup inferior-saw nil
  "Run saw in an Emacs buffer."
  :group 'saw-script
  :version "1")

(defcustom inferior-saw-program "saw"
  "Program name for invoking saw in Inferior Saw mode."
  :type 'string
  :group 'inferior-saw)

(defcustom inferior-saw-prompt "^sawscript> *"
  "Regexp to recognize prompts in the Inferior Saw mode.
Defaults to \"^sawscript> *\".
This variable is used to initialize `comint-prompt-regexp' in the
inferior saw buffer.

This variable is only used if the variable
`comint-use-prompt-regexp' is non-nil."
  :type 'regexp
  :group 'inferior-saw)

(defvar inferior-saw-buffer nil "The current inferior-saw process buffer.")

(defvar inferior-saw-mode-map
  (let ((map (copy-keymap comint-mode-map)))
    ;(define-key map "\C-x\C-e" 'saw-eval-last-thing)
    (define-key map "\C-c\C-l" 'saw-load-file)
    ;(define-key map "\C-c\C-a" 'lisp-show-arglist)
    ;(define-key map "\C-c\C-d" 'lisp-describe-sym)
    ;(define-key map "\C-c\C-f" 'lisp-show-function-documentation)
    ;(define-key map "\C-c\C-v" 'lisp-show-variable-documentation)
    map))

;;; These commands augment sawscript mode, so you can process SAWscript in
;;; the source files.
(define-key saw-script-mode-map "\M-\C-x"  'saw-eval-defun)     ; GNU convention
(define-key saw-script-mode-map "\C-x\C-e" 'saw-eval-last-sexp) ; GNU convention
(define-key saw-script-mode-map "\C-c\C-e" 'saw-eval-defun)
(define-key saw-script-mode-map "\C-c\C-r" 'saw-eval-region)
;; (define-key saw-script-mode-map "\C-c\C-n" 'saw-eval-form-and-next)
(define-key saw-script-mode-map "\C-c\C-z" 'switch-to-saw)
(define-key saw-script-mode-map "\C-c\C-l" 'saw-load-file)
;(define-key saw-script-mode-map "\C-c\C-a" 'lisp-show-arglist)
;(define-key saw-script-mode-map "\C-c\C-d" 'lisp-describe-sym)
;(define-key saw-script-mode-map "\C-c\C-f" 'lisp-show-function-documentation)
;(define-key saw-script-mode-map "\C-c\C-v" 'lisp-show-variable-documentation)
(define-key saw-script-mode-map "\C-\M-a" 'beginning-of-saw-form)
(define-key saw-script-mode-map "\C-\M-e" 'end-of-saw-form)

(defvar inferior-saw-mode-hook '()
  "Hook for customizing Inferior Saw mode.")

(define-derived-mode inferior-saw-mode comint-mode "Inferior Saw"
  "Major mode for interacting with an inferior saw process.
Runs a saw interpreter as a subprocess of Emacs, with I/O through an
Emacs buffer.  Variable `inferior-saw-program' controls which Saw interpreter
is run.

For information on running multiple processes in multiple buffers, see
documentation for variable `inferior-saw-buffer'.

\\{inferior-saw-mode-map}

Customization: Entry to this mode runs the hooks on `comint-mode-hook' and
`inferior-saw-mode-hook' (in that order).

You can send text to the inferior Saw process from other buffers containing
SAWscript source, if they are in SawScript mode.

    `switch-to-saw' switches the current buffer to the Saw process buffer.
    `saw-eval-defun' sends the current SAWscript form to the Saw process.
    `saw-eval-region' sends the current region to the Saw process (but the
       saw interpreter only accepts one SAW form at a time, so the region can only
       include one form).

    Prefixing the eval commands with a \\[universal-argument] causes 
    switch to the saw process buffer after sending the text.

    A \"SAWscript form\" is a block of text starting with an alphabetic character
    at the start of a line, up to its closing semicolon, however many lines that may be.

Commands:\\<inferior-saw-mode-map>
\\[comint-send-input] after the end of the process' output sends the text from the
    end of process to point.
\\[comint-send-input] before the end of the process' output copies the sexp ending at point
    to the end of the process' output, and sends it.
\\[comint-copy-old-input] copies the sexp ending at point to the end of the process' output,
    allowing you to edit it before sending it.
If `comint-use-prompt-regexp' is nil (the default), \\[comint-insert-input] on old input
   copies the entire old input to the end of the process' output, allowing
   you to edit it before sending it.  When not used on old input, or if
   `comint-use-prompt-regexp' is non-nil, \\[comint-insert-input] behaves according to
   its global binding.
\\[backward-delete-char-untabify] converts tabs to spaces as it moves back.
\\[lisp-indent-line] indents for Lisp; with argument, shifts rest
    of expression rigidly with the current line.
\\[indent-sexp] does \\[lisp-indent-line] on each line starting within following expression.
Paragraphs are separated only by blank lines.
If you accidentally suspend your process, use \\[comint-continue-subjob]
to continue it."
  (setq comint-prompt-regexp inferior-saw-prompt)
  (setq mode-line-process '(":%s"))
  ;; (saw-mode-variables t)
  ;; (setq comint-get-old-input (function saw-get-old-input))
  ;; (setq comint-input-filter (function saw-input-filter))
  )


(defun saw-eval-region (start end &optional and-go)
  "Send the current region to the inferior Saw process.
Prefix argument means switch to the Saw buffer afterwards.

Note that Saw only allows for one form to be entered at a time,
so the region should consist of only one SawScript form."
  (interactive "r\nP")
  ;; we need to put continuation marks '\' at the end of each line but the last
  (let ((raw-str (buffer-substring-no-properties start end)))
    (comint-send-string (inferior-saw-proc)
       (replace-regexp-in-string (regexp-quote "\n") " \\\n" raw-str nil 'literal)))
  ;; (comint-send-string (inferior-saw-proc) "; print \"OK\"; \n")
  (comint-send-string (inferior-saw-proc) "\n")
  (if and-go (switch-to-saw t)))

(defun saw-eval-defun (&optional and-go)
  "Send the current SAWscript form to the inferior Saw process.
Prefix argument means switch to the Saw buffer afterwards.
A SAWscript form is defined to start with an alphabetic character at the start of a line,
continuing through balanced parentheses to a semicolon."
  (interactive "P")
  (save-excursion
    (beginning-of-saw-form)
    (let ((start (point)))
      (end-of-saw-form)
      (saw-eval-region start (point))))
  (if and-go (switch-to-saw t))) ;; outside save-excursion, in case that matters

(defvar start-of-saw-form-re "^[a-zA-Z]") ;; alphabetic at start of line

(defun beginning-of-saw-form ()
  (interactive)
  (unless (looking-at start-of-saw-form-re)
    (re-search-backward start-of-saw-form-re)))


(defun end-of-saw-form ()
  (interactive)
  (while (not (looking-at "[[:space:]]*;"))
    (forward-sexp))
  (re-search-forward "[[:space:]]*;")
  )

;; (defun end-of-saw-form ()
;;   (interactive)
;;   (unless (looking-at "[[:space:]]*;")
;;     (forward-sexp)
;;     (end-of-saw-form))
;;   ;; (re-search-forward "[[:space:]]*;")
;;   )

(defun switch-to-saw (eob-p)
  "Switch to the inferior Saw process buffer.
With argument, positions cursor at end of buffer."
  (interactive "P")
  (if (get-buffer-process inferior-saw-buffer)
      (let ((pop-up-frames
	     ;; Be willing to use another frame
	     ;; that already has the window in it.
	     (or pop-up-frames
		 (get-buffer-window inferior-saw-buffer t))))
	(pop-to-buffer inferior-saw-buffer))
      (run-saw inferior-saw-program))
  (when eob-p
	 (push-mark)
    (goto-char (point-max))))

(defalias 'run-saw 'inferior-saw)
(defun inferior-saw (cmd)
  "Run an inferior saw process, input and output via buffer `*inferior-saw*'.
If there is a process already running in `*inferior-saw*', just switch
to that buffer.
With argument, allows you to edit the command line (default is value
of `inferior-saw-program').  Runs the hooks from
`inferior-saw-mode-hook' (after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"
  (interactive (list (if current-prefix-arg
			 (read-string "Run saw: " inferior-saw-program)
		       inferior-saw-program)))
  (if (not (comint-check-proc "*inferior-saw*"))
      (let ((cmdlist (split-string cmd)))
	(set-buffer (apply (function make-comint)
			   "inferior-saw" (car cmdlist) nil (cdr cmdlist)))
	(inferior-saw-mode)))
  (setq inferior-saw-buffer "*inferior-saw*")
  (pop-to-buffer-same-window "*inferior-saw*"))

;;  "Returns the current inferior Saw process.
;; See variable `inferior-saw-buffer'."
(defun inferior-saw-proc ()
  (let ((proc (get-buffer-process (if (derived-mode-p 'inferior-saw-mode)
				      (current-buffer)
				    inferior-saw-buffer))))
    (or proc
	(error "No Saw subprocess; see variable `inferior-saw-buffer'"))))


(defvar saw-prev-l/c-dir/file nil
  "Record last directory and file used in loading.
This holds a cons cell of the form `(DIRECTORY . FILE)'
describing the last `saw-load-file' command.")

(defun saw-load-file (file-name)
  "Load a Saw file into the inferior Saw process."
  (interactive (comint-get-source "Load SAWscript file: " saw-prev-l/c-dir/file
				  '(saw-script-mode) t))
  (comint-check-source file-name) ; Check to see if buffer needs saved.
  (setq saw-prev-l/c-dir/file (cons (file-name-directory    file-name)
				    (file-name-nondirectory file-name)))
  (comint-send-string (inferior-saw-proc)
		      (format "include \"%s\";\n" file-name))
  (switch-to-saw t))
