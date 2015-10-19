(set-logic SLIA)

(define-fun p ((x (Ref Int)) (a Int) (y (Ref Int)) (b Int)) Bool 
	(and (sep (pto x a) (pto y b)) 
		 (< a b)
	)
)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and (sep (p x a y b) (pto z c)) 
			 (sep (pto x a) (p y b z c))
		)
)

(assert (not ((sep (pto y b) (p x a z c)))))

(check-sat)