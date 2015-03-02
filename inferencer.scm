(load "mk/mk.scm")
(load "mk/test-check.scm")

; Type inferencer from miniKanren uncourse hangout #14, March 1, 2015.

; Assuming that term is in the condition position
; of an if-statement, what propositions do we learn about
; the then and else branches?
(define (infer-props term then-prop else-prop)
  (conde
    [(== #f term)
     (== 'ff then-prop)
     (== 'tt else-prop)]
    [(conde
       [(== #t term)]
       [(numbero term)])
     (== 'tt then-prop)
     (== 'ff else-prop)]
    [(symbolo term)
     (== `(,term (not (val #f))) then-prop)
     (== `(,term (val #f)) else-prop)]))

; Look up var in the proposition environment and find
; type information res.
(define (lookupo var env res)
  (conde
    [(fresh (d)
       (== `((,var ,res) . ,d) env))]
    [(fresh (aa ad d)
       (=/= var aa)
       (== `((,aa ,ad) . ,d) env)
       (lookupo var d res))]))

; Prove that var is compatible with type given the proposition environment
(define (proveo prop-env var type)
  (conde
    [(fresh (t1)
       (lookupo var prop-env t1)
       (subtypeo t1 type))]))

(define (booleano b)
  (conde
    [(== #t b)]
    [(== #f b)]))

; Succeed if child-type is a subtype of parent-type,
; like (var #f) is a subtype of 'bool.
(define (subtypeo child-type parent-type)
  (conde
    [(== child-type parent-type)]
    [(fresh (b)
       (== `(val ,b) child-type)
       (conde
         [(booleano b)
          (== 'bool parent-type)]
         [(numbero b)
          (== 'num parent-type)]))]
    [(fresh (t1 t2)
       (== `(U ,t1 ,t2) child-type)
       (subtypeo t1 parent-type)
       (subtypeo t2 parent-type))]))

; Union type constructor. We might need to make this
; smarter in the future.
(define (uniono t1 t2 union-type)
  (conde
    [(== t1 t2)
     (== t1 union-type)]
    [(=/= t1 t2)
     (== `(U ,t1 ,t2) union-type)]))

; Given term and the proposition environment, infer the most
; specific type for the term. If you want to check compatiblity
; of the term's type with a given type, use the subtype relation
; with the type argument of this relation.
(define (infer term prop-env type)
  (conde
    [(== #f term)
     (== '(val #f) type)]
    [(== #t term)
     (== '(val #t) type)]
    [(numbero term)
     (== `(val ,term) type)]
    [(fresh (condition then else then-prop
             else-prop cond-type t1 t2)
       (== `(if ,condition ,then ,else) term)
       (infer condition prop-env cond-type)
       (subtypeo cond-type 'bool)
       (infer-props condition then-prop else-prop)
       (infer then `(,then-prop . ,prop-env) t1)
       (infer else `(,else-prop . ,prop-env) t2)
       (uniono t1 t2 type))]
    [(fresh (arg argtype body prop-env^ res-type)
       (== `(lambda (,arg : ,argtype) ,body) term)
       (== `((,arg ,argtype) . ,prop-env) prop-env^)
       (infer body prop-env^ res-type)
       (subtypeo `(,argtype -> ,res-type) type))]
    [(fresh ()
       (symbolo term)
       (proveo prop-env term type))]
    [(fresh (expr expr-type)
       (== `(inc ,expr) term)
       (infer expr prop-env expr-type)
       (subtypeo expr-type 'num)
       (== 'num type))]))

(test "plain #t"
  (run* (q)
    (infer #t '() q))
  '((val #t)))

(test "plain #f"
  (run* (q)
    (infer #f '() q))
  '((val #f)))

(test "if, type #t"
  (run* (q)
    (infer `(if #t #t #t) '() q))
  '((val #t)))

(test "another if, type #t"
  (run* (q)
    (infer `(if #f #t #t) '() q))
  '((val #t)))

(test "if, union #t #f"
  (run* (q)
    (infer `(if #t #t #f) '() q))
  '((U (val #t) (val #f))))


(test "plain number"
  (run* (q)
    (infer 1 '() q))
  '((val 1)))

(test "if, type (val 1)"
  (run* (q)
    (infer `(if #t 1 1) '() q))
  '((val 1)))

(test "inference doens't include subtype"
  (run* (q)
    (infer 1 '() 'num))
  '())

(test "inc should accept a number and return a number"
  (run* (q)
    (infer '(inc 1) '() q))
  '(num))

(test "inc of boolean should fail"
  (run* (q)
    (infer '(inc #t) '() q))
  '())

(test "function type"
  (run* (q)
    (infer '(lambda (arg : num) (inc arg)) '() q))
  '((num -> num)))

(test "incorrect typing inside function definition should cause failure"
  (run* (q)
    (infer '(lambda (arg : num) (inc #f)) '() q))
  '())

(test "should fail when argument used contrary to type declaration"
  (run* (q)
    (infer '(lambda (arg : (val #f)) (inc arg)) '() q))
  '())

(test "should fail when one element of arg union type is incompatible with usage"
  (run* (q)
    (infer '(lambda (arg : (U (val #f) num)) (inc arg)) '() q))
  '())

; Not implemented yet.
;
; prop-env at if: (arg (U (val #f) num))
; prop-env at (inc arg): ((arg (U (val #f) num))
;                         (arg (not (val #f))))
;
; need to combine information from the two propositions to derive the proposition (arg num).
;
; This will involve writing a function env+ that takes a proposition environment and a proposition
; and returns a new proposition environment with the derived (positive) proposition. This is the proposition
; that the variable case will access.
; the `then` case then becomes
; (fresh ()
;   (env+ prop-env then-prop prop-env^)
;   (infer then prop-env^ t1)
; and similarly for the else branch.
;
(test "should infer correct branch of union from if condition"
  (run* (q)
    (infer '(lambda (arg : (U (val #f) num))
              (if arg (inc arg) 0)) '() q))
  ; I'm not 100% certain of this expected output.
  '(((U (val #f) num) -> (U num 0))))

