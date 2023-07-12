(set-logic QF_UFLIA)
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
;; validity check for c
(assert (not |Potato.Kitten.c.valid|))
(check-sat)
(get-value (|Potato.Kitten.a.value|))
(get-value (|Potato.Kitten.a.valid|))
(get-value (|Potato.Kitten.b.value|))
(get-value (|Potato.Kitten.b.valid|))
(get-value (|Potato.Kitten.c.value|))
(get-value (|Potato.Kitten.c.valid|))
(exit)
