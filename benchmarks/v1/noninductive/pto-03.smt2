(set-logic SEPLOGLIA)

(declare-sort Ref 1)

(declare-const x (Ref Int))
(declare-const y (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (and (pto x a) (pto y b)))

(assert (not (and (= x y) (= a b))))

(check-sat)