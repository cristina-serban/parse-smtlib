(set-logic SEPLOGIA)

(declare-const x (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (and (pto x a) (pto x b)))

(assert (not (= a b)))

(check-sat)