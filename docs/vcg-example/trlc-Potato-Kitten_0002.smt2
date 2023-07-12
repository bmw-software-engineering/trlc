(set-logic QF_UFNIA)
(set-option :produce-models true)

(declare-fun |trlc.matches| (String String) Bool)
;; value for a declared on potato.rsl:4:3
(declare-const |Potato.Kitten.a.value| Int)
(define-const |Potato.Kitten.a.valid| Bool true)
;; value for b declared on potato.rsl:5:3
(declare-const |Potato.Kitten.b.value| Int)
(define-const |Potato.Kitten.b.valid| Bool true)
;; value for c declared on potato.rsl:6:3
(declare-const |Potato.Kitten.c.value| Int)
(define-const |Potato.Kitten.c.valid| Bool true)
(assert |Potato.Kitten.a.valid|)
;; result of a > 17 at potato.rsl:10:5
(define-const |tmp.1| Bool (> |Potato.Kitten.a.value| 17))
(assert |tmp.1|)
(assert |Potato.Kitten.a.valid|)
(assert |Potato.Kitten.b.valid|)
(assert |Potato.Kitten.c.valid|)
;; result of b * c at potato.rsl:10:27
(define-const |tmp.3| Int (* |Potato.Kitten.b.value| |Potato.Kitten.c.value|))
;; result of a + b * c at potato.rsl:10:23
(define-const |tmp.4| Int (+ |Potato.Kitten.a.value| |tmp.3|))
;; division by zero check for 100 / a + b * c
(assert (not (not (= |tmp.4| 0))))
(check-sat)
(get-value (|Potato.Kitten.a.value|))
(get-value (|Potato.Kitten.a.valid|))
(get-value (|Potato.Kitten.b.value|))
(get-value (|Potato.Kitten.b.valid|))
(get-value (|Potato.Kitten.c.value|))
(get-value (|Potato.Kitten.c.valid|))
(exit)
