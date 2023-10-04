(set-logic QF_FP)
(set-option :produce-models true)

(define-const one       Float32 ((_ to_fp 8 24) RNE 1.0))
(define-const point_one Float32 ((_ to_fp 8 24) RNE 0.1))

(define-const expect Float32 ((_ to_fp 8 24) RNE 0.8))

(define-const sum Float32
  (fp.add RNE
	  (fp.add RNE
		  (fp.add RNE
			  (fp.add RNE
				  (fp.add RNE
					  (fp.add RNE
						  (fp.add RNE
							  point_one point_one)
						  point_one)
					  point_one)
				  point_one)
			  point_one)
		  point_one)
	  point_one))

(define-const goal Bool (fp.eq sum expect))
(assert (not goal))

(check-sat)
(get-value (sum))
(get-value (expect))
(exit)
