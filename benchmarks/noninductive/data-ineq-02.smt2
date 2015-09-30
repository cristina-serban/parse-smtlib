(set-logic SLIA)

(declare-datatype Node ((empty) (node_cons (data Int) (ref (Ref Node)))))

(define-fun q ((x (Ref Node)) (a Int) (x1 (Ref Node)) (y (Ref Node)) (b Int) (y1 (Ref Node))) Bool 
	(and (sep (pto x (node_cons a x1)) (pto y (node_cons b y1))) (< a b)) 
)

(define-fun p ((x (Ref Node)) (y (Ref Node))) Bool 
	(exists ((a Int) (b Int) (z (Ref Node))) (q x a y y b z))
)

(declare-const x (Ref Node))
(declare-const y (Ref Node))
(declare-const z (Ref Node))
(declare-const t (Ref Node))

(declare-const a Int)
(declare-const c Int)

(assert (and (sep (p x y) (pto z (node_cons c t))) 
			 (sep (pto x (node_cons a y)) (p y z))
		)
)

(assert (not (exists ((b Int)) 
				(sep (pto y (node_cons b z)) (q x a y z c t))
			 )
		)
)

(check-sat)