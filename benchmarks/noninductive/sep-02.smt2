(set-logic SEPLOGIA)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (sep (pto x a) (pto y b) (pto z c)))

(assert (or (= x y) (= y z) (= x z)))

(check-sat)