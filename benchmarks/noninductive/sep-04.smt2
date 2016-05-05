(set-logic SEPLOGIA)

(declare-const x (Ref Int))
(declare-const y (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (sep (or (pto x a) (pto y b)) 
			 (or (pto x a) (pto y b))
		)
)

(assert (not (sep (pto x a) (pto y b))))

(check-sat)