(set-logic SEPLOGIA)

(declare-datatype Node ((empty) (node_cons (data Int) (ref (Ref Node)))))

(define-fun q ((x (Ref Node)) (a Int) (x1 (Ref Node)) (y (Ref Node)) (b Int) (y1 (Ref Node))) Bool 
	(and (sep (pto x (node_cons a x1)) (pto y (node_cons b y1))) (< a b)) 
)

(declare-const x (Ref Node))
(declare-const y (Ref Node))
(declare-const z (Ref Node))
(declare-const t (Ref Node))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and (sep (q x a y y b z) (pto z (node_cons c t))) 
			 (sep (pto x (node_cons a y)) (p y b z z c t))
		)
)

(assert (not (sep (pto y (node_cons b z)) (q x a y z c t))))

(check-sat)