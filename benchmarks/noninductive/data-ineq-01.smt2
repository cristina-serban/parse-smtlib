(set-logic SLIA)

(define-fun p ((x (Ref Int)) (y (Ref Int))) Bool 
	(exists ((a Int) (b Int)) 
		(and (sep (pto x a) (pto y b)) 
			 (< a b)
		)
	)
)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const c Int)

(assert (and (sep (p x y) (pto z c)) 
			 (sep (pto x a) (p y z))
		)
)

(assert (not (exists ((b Int)) 
				(sep (pto y b) (p x z))
			 )
		)
)

(check-sat)