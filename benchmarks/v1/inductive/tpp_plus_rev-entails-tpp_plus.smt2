(set-logic SEPLOG)

(declare-sort Ref 1)

(declare-datatype tpp_t ((empty) (tpp_cons (left (Ref tpp_t)) (right (Ref tpp_t)) (parent (Ref tpp_t)))))

(define-fun-rec tpp_plus ((x (Ref tpp_t)) (back (Ref tpp_t))) Bool
    (or (pto x (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) back))
        (exists ((y (Ref tpp_t)) (z (Ref tpp_t)))
            (sep (pto x (tpp_cons y z back))
                 (tpp_plus y x)
                 (tpp_plus z x))
        )
    )
)

(define-fun-rec tpp_aux ((x (Ref tpp_t)) (down (Ref tpp_t)) (top (Ref tpp_t)) (b (Ref tpp_t))) Bool
    (or (exists ((up (Ref tpp_t)) (right (Ref tpp_t)))
            (sep (pto x (tpp_cons down right up))
                 (tpp_plus right x)
                 (tpp_aux up x top b))
        )
        (exists ((up (Ref tpp_t)) (left (Ref tpp_t)))
            (sep (pto x (tpp_cons left down up))
                 (tpp_plus left x)
                 (tpp_aux up x top b))
        )
        (exists ((right (Ref tpp_t)))
            (and (= x top)
                 (sep (pto x (tpp_cons down right b))
                       (tpp_plus right x))
            )
        )
        (exists ((left (Ref tpp_t)))
            (and (= x top)
                 (sep (pto x (tpp_cons left down b))
                       (tpp_plus left x))
            )
        )
    )
)

(define-fun-rec tpp_plus_rev ((top (Ref tpp_t)) (b (Ref tpp_t))) Bool
    (or (pto top (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) b))
        (exists ((x (Ref tpp_t)) (up (Ref tpp_t)))
            (sep (pto x (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) up))
                 (tpp_aux up x top b))
        )
    )
)

(declare-const x (Ref tpp_t))
(declare-const y (Ref tpp_t))

(assert (tpp_plus_rev x y))
(assert (not (tpp_plus x y)))

(check-sat)