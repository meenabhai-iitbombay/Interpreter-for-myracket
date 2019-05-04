#lang racket
(require racket/struct)
(provide (all-defined-out))
(require "defs.rkt")
(require "examples.rkt")

;;;;I am changing something
(define stacks (make-vector 100))
(define stacksindex 0)

;;Global definitions. A counter that tracks the framenumber
(define framenumber 0)

;The stack and its operations. I have decided to make the stack a global.
(define stack '())
(define (push frame) (set! stack (cons frame stack)))
(define (pop) (if (null? stack) (error "Empty stack")
                        (set! stack (cdr stack))))
(define (top) (if (null? stack) (error "Empty stack")
                        (car stack)))


;createframe creates a new frame. It gets its number from
;;framenumber and as a side effect increases framenumber
(define (createframe hashtable parent) ;hastable gives the initial bindings
   (let ([oldframenumber framenumber])
     (begin (set! framenumber (+ 1 framenumber))
            (frame oldframenumber hashtable parent))))

;This creates the global frame, which, in our case, contains
;empty bindings.
(push (createframe (make-hash '()) (emptyframe)))

;This interprets a program. It uses the following function processdef.
(define (eval-program prog)
         (match prog
           [(pgm deflist)
            (begin
             (let ([l (map (lambda (x) (processdef x (top))) deflist)])
;              (newline) (newline)
;               (display (last l))
              (return-value-of-main (top))))]))

;;processdef describes how each definition is processed and added to
;;the frame fr.
(define (processdef defn fr)
  (match defn    
    [(def v/f exp)
     (let ([bindings (frame-bindings fr)])
       (begin
         ;(display 0)
         ;after this line are developer the last commented line is real
;         (let ([e (eval-exp exp)])
;           (newline)
;           (display "&&&&&&&&&&&&&&&&")
;           (display (frame-number (top))) (display (string-append (~a v/f) " :"))
;           (newline)
;           (display e)
;           (hash-set! bindings v/f e)
       (hash-set! bindings v/f (eval-exp exp))
       (set-frame-bindings! fr bindings))
       )]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (processletdef defn new-fr)
  (match defn    
    [(def v/f exp)
     (let ([bindings (frame-bindings new-fr)])
       (begin
         ;(display 0)
         ;after this line are developer the last commented line is real
;         (let ([e (eval-exp exp)])
;           (newline)
;           (display "&&&&&&&&&&&&&&&&")
;           (display (frame-number (top))) (display (string-append (~a v/f) " :"))
;           (newline)
;           (display e)
;           (hash-set! bindings v/f e)
       (hash-set! bindings v/f (eval-exp exp))
       (set-frame-bindings! new-fr bindings))
       )]))

;; We have said that the result of the program is the value of
;; the symbol main. main must be a defined symbol in each program.
(define (return-value-of-main frame)
  (hash-ref! (frame-bindings frame) 'main "main not found"))

;; The expression evaluator is the heart of the interpreter.
;; It will use the functions below
(define (eval-exp exp)
; (newline)
;  (display "@@@@@@@")
;  (newline)
;  (display exp)
;  (newline)
  (cond [(symbol? exp)
         (let ([sym-fr (search exp (top))])
           (begin ;(display sym-fr) (newline) (display exp)
           (if (equal? sym-fr (emptyframe))
               (begin
                 ;(displayln "this is symbol")
                 (displayln exp) 
               (error "Symbol not found"))
               (let* ([user-list (hash->list (frame-bindings sym-fr))]
                      [item (findf (lambda (x) (equal? (car x) exp)) user-list)])
               (if (equal? item #f)
                   (error "symbol not found 2")
                  (begin ;(display user-list) (display item) (newline)
                         (cdr item)))))))]
        [(boolean? exp) exp]
        [(number? exp) exp]
        [(list? exp) exp]
        [(string? exp) exp]
        [else (match exp
                [(uexp op exp1) (op (eval-exp exp1))]
                [(bexp op exp1 exp2) (op (eval-exp exp1) (eval-exp  exp2))]
                [(lam varlist exp) (closure (lam varlist exp) (top))]
                [(app exp1 explist)
                 ;(display "hi")
                 (let ([exp1 (eval-exp exp1)]
                       [explist (map (lambda (x) (eval-exp x)) explist)])
                 (begin
                 (push (createframe (make-hash '()) (closure-frame exp1)))
                 ;(display "bye")
                 (let*([exp2 (closure-lambda exp1)]
                       [varlist (lam-varlist exp2)]
                       [valuelist explist]
                       [justforsake (deflist varlist valuelist)]
                       [returnvalue (eval-exp (lam-exp exp2))])
                   (begin (pop)
                          returnvalue))))]
                ;...and so on, fill in these...
                [(iff cond exp1 exp2)
                 (begin
;                   (newline)
;                   (display "hi")
;                   (display (eval-exp cond))
;                   (display (eval-exp exp1))
;                   (newline) (newline)
                 (if (eval-exp cond)
                     (eval-exp exp1)
                     (eval-exp exp2))
                 )]
                [(lett deflist exp)
                 (let*  ([new-fr (createframe (make-hash '()) (top))]
                         [just1  (map (lambda (x) (processletdef x  new-fr)) deflist)]
                         [just2 (push new-fr)]
                         [e (eval-exp exp)])
                   (begin (pop)
                          e))
;                 (begin
;                   (push (createframe (make-hash '()) (top)))
;                   ;(displayln "1st") (displayln (car deflist))
;                   (map (lambda (x) (processdef x (top))) deflist)
;                   ;(displayln "mid")
;                   (let ([e  (eval-exp exp)])
;                     (begin
;                       ;(displayln "2nd")
;                       (pop)
;                       e)))
                 ]
                [(lets deflist exp)
                 (if (null? deflist) (eval-exp exp)
                 (if (null? (cdr deflist))
                     (eval-exp (lett deflist exp))
                 (eval-exp (lett (list (car deflist)) (lets (cdr deflist) exp)))))]
                [(sett var exp)
                 (let ([var-fr (search var (top))])
                   (if (equal? var-fr (emptyframe))
                       (error "Symbol not found")
                       (let ([bindings (frame-bindings var-fr)])
                         (begin
                         (hash-set! bindings var (eval-exp exp))
                         (set-frame-bindings! var-fr bindings)))))]
                [(defexp deflist exp)
                 (begin
                   (map (lambda (x) (processdef x (top))) deflist)
                   (eval-exp exp))]
                [(beginexp l) ;(begin (display "till")
                                     (process-beginexp l);)
                              ]
                
                [(debugexp) (begin
                 (vector-set! stacks stacksindex stack)
                 (set! stacksindex (+ 1 stacksindex)))]
;                [(debugexp) (begin
;                             ; (displayln "debug")
;                              (print-current-environment (top))
;                              )]
                )]))

;;An auxilliary function that processes a begin expression
(define (process-beginexp explist) 
  (match explist
   ['() void]
   [l (let* ([n  (map (lambda (x) (eval-exp x)) l)]
            [e (last n)])
        (cond [(not (equal? e void)) e])
        ;(display "non-null")
        ;(display n)
       ;I think after this we have to do frame change,but think about it later
     )]))

;;An auxilliary function that processes a let expression.
;;The let definitions are in deflist, and the let body is exp.
(define (process-lets deflist exp)
  (match deflist
    ["a" '()]))

;;Prints the current environment running through a chain of frames.
;;Note that my struct definitions are such that if fr is a frame,
;;then (displayln fr) will print the frame in the format that I have
;;shown. 
(define (print-current-environment fr)
  (if (equal? fr (emptyframe))
      void
      (begin
  (displayln "@@@@@@@@@@@@@@@@@@@@@@@")
  (displayln fr)
  (print-current-environment (frame-parent fr)))))

;;Search for the symbol sym in an environment that starts with the frame
;;fr. We shall make search return either the  emptyframe
;;or the frame containing the symbol (note, not the value of the
;;symbol itself.

(define (search sym fr)
 (cond [(equal? (emptyframe) fr) fr]
       [(hash-has-key? (frame-bindings fr) sym) fr]
       [else (search sym (frame-parent fr))]))
               
;;;;;;;;;;;;;;;;;;;;
(define (deflist varlist valuelist) ;only for app
  (define (helper l1 l2 bindings)
    (cond [(null? l1) (set-frame-bindings! (top) bindings)]
          [else (begin 
                       (hash-set! bindings (car l1) (car l2))
                       (helper (cdr l1) (cdr l2) bindings))]))
  (cond [(= (length varlist) (length valuelist))
   (let ([bindings (frame-bindings (top))])
         (helper varlist valuelist bindings))]
        
        [else (error (string-append
                      "MY arity mismatch;
the expected number of arguments does not match the given number
expected:"(~a (length varlist)) "
given:" (~a (length valuelist))
  "arguments...:"))]))

;;;;;;;;;;;;;;;;;;;;;
(define (cleanup)
  (set!  stacks (make-vector 100))
  (set! stacksindex 0)
  (set! framenumber 0)
  (set! stack '())
  (push (createframe (make-hash '()) (emptyframe))))
