#|
PLT Redex demo by Yufei Cai
Date: 15.04.13
Place: 05D09 SR V

PLT Redex homepage and examples
http://redex.racket-lang.org

PLT Redex manual
http://docs.racket-lang.org/redex/The_Redex_Reference.html

This file follows ideas in the following two:
https://github.com/klauso/PLT2012/blob/master/lecturenotes/02-ae.scala
https://github.com/klauso/PLT2012/blob/master/lecturenotes/05-fae.scala
|#

#lang racket

(require redex)

;; 02-ae.scala:20

;; (define-language lang-name
;;    non-terminal-def ...)

(define-language AE
  ;; Exp ::= Num | Add | Mul | Id
  (Exp Num Add Mul Id)
  ;; Num ::= ... | -2 | -1 | 0 | 1 | 2 | ...
  (Num integer)
  ;; Add ::= Exp + Exp
  (Add (Exp + Exp))
  ;; Mul ::= Exp * Exp
  (Mul (Exp * Exp))
  ;; Id ::= a | b | ... | ab | ac | ...
  (Id (variable-except + *)))

(define malformed '(+ (* x 2) (+ y y)))
(define test0 '((x * 2) + (y + y)))
(define test1 '((9 * 2) + (12 + 12)))

;; (redex-match lang pattern any)
;; (test-equal e1 e2)

(test-equal (redex-match AE Exp malformed) #f)

;; (test-predicate p? e)

(test-predicate identity (redex-match AE Exp test0))
(test-predicate identity (redex-match AE Exp test1))

;; Evaluation context is a built-in concept in Redex.
;; We use it to encode congruence reduction rules here.

;; (define-extended-language extended-lang base-lang
;;   non-terminal-def ...)

(define-extended-language eval-ctx AE
  (E hole
     (E + Exp) (Exp + E)
     (E * Exp) (Exp * E)))

(define arith
  (reduction-relation
   eval-ctx ; AE
   (reduce (Num_1 + Num_2) ,(+ (term Num_1) (term Num_2)) "δ+")
   (reduce (Num_1 * Num_2) ,(* (term Num_1) (term Num_2)) "δ*")
   with
   [(--> (in-hole E e1) (in-hole E e2)) (reduce e1 e2)]))

;; Opens a GUI to show all possible reductions from a term

;; (traces arith test1)
;; (traces arith test0)

;; It is awkward to thread an environment down to evaluate open
;; terms such as test0. So instead of
;;
;;     02-ae.scala:55
;;
;; we will proceed directly to a full-blown λ-calculus to deal
;; with names:
;;
;;     05-fae.scala:53

(define-extended-language FAE AE
  ;; Syntax
  (Exp Num Add Mul Id Fun App)
  (Id (variable-except + * λ))
  (Fun (λ Id Exp))
  (App (Exp Exp))
  ;; Evaluation context
  (E hole
     (E + Exp) (Exp + E)
     (Exp * E) (E * Exp)
     (E Exp) (Exp E)))

;; How should we write `test0 with x = 9 and y = 12`?
;;
;; (((λ x (λ y ,test0)) 9) 12)
;;
;; This is complicated. Often it is error-prone to write
;; expressions in a concrete syntax with a simple definition.
;; Syntactic sugars simplify terms without complicating their
;; reduction rules.

;; (define-metafunction language
;;   metafunction-contract
;;   [(name pattern ...) term metafunction-extras ...]
;;   ...)

;; Syntactic sugar for multivariate lambda abstraction
;; (λ* (x y) Exp) ::= (λ x (λ y Exp))

(define-metafunction FAE
  λ* : (Id ...) Exp -> Exp
  [(λ* (Id_0 Id_1 ...) Exp) (λ Id_0 (λ* (Id_1 ...) Exp))]
  [(λ* () Exp) Exp])

(test-equal (term (λ* (x y) z)) '(λ x (λ y z)))

;; Syntactic sugar for multivariate application
;; (@ e1 e2 e3) ::= ((e1 e2) e3)

(define-metafunction FAE
  @ : Exp ... -> Exp
  [(@ Exp_0 Exp_1) (Exp_0 Exp_1)]
  [(@ Exp_0 Exp_1 Exp_2 ...) (@ (Exp_0 Exp_1) Exp_2 ...)])

(test-equal (term (@ x y z)) '((x y) z))

(define test2 (term (@ (λ* (x y) ,test0) 9 12)))
(test-equal test2 '(((λ x (λ y ((x * 2) + (y + y)))) 9 ) 12))

;; Evaluation by substitution
;;
;;     05-fae.scala:177

(define βδ
  (extend-reduction-relation
   arith FAE
   (reduce ((λ Id Exp_0) Exp_1) (subst Id Exp_1 Exp_0) "β")
   with
   [(--> (in-hole E e1) (in-hole E e2)) (reduce e1 e2)]))

;; (traces βδ '((λ x x) (3 + 5)))

(define-metafunction FAE
  subst : Id Exp any -> any
  [(subst Id Exp Id) Exp]
  [(subst Id Exp Id_1) Id_1]
  [(subst Id Exp (λ Id Exp_0)) (λ Id Exp_0)]
  [(subst Id Exp (λ Id_0 Exp_0))
   (λ Id_fresh (subst Id Exp (subst Id_0 Id_fresh Exp_0)))
   (where Id_fresh ,(variable-not-in (term (Id Exp Exp_0))
                                     (term Id_0)))]
  ;; Congruence on App, Add, Mul
  [(subst Id Exp (any ...)) ((subst Id Exp any) ...)]
  [(subst Id Exp any) any])

;; (traces βδ '((λ x x) (3 + 5)))
;; (traces βδ test2)

(test-predicate (λ (results) (member 42 results))
                (apply-reduction-relation* βδ test2))

;; Redex supports automatic attempts at refuting properties of a language.
;; For example: Does all FAE expressions evaluate to a number?

;; (redex-check language pattern property-expr kw-arg ...)

(redex-check
 FAE Exp
 (not (empty? (filter number? (apply-reduction-relation* βδ (term Exp))))))

;; Let's try to refute Church-Rosser property on terms that evaluate to
;; a number.

(define (CR/Num? e)
  (>= 1 (length (remove-duplicates
                 (filter number?
                         (apply-reduction-relation* βδ e))))))

(redex-check FAE Exp (CR/Num? (term Exp)))