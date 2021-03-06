(set-logic SEPLOG)

(declare-sort Ref 1)

(declare-datatype tll_t ((empty) (tll_cons (left (Ref tll_t)) (right (Ref tll_t)) 
                                            (parent (Ref tll_t)) (next (Ref tll_t)))))

(define-fun-rec tll_plus ((root (Ref tll_t)) (parent (Ref tll_t)) (ll (Ref tll_t)) (lr (Ref tll_t))) Bool
    (or (and (pto root (tll_cons (as nil (Ref tll_t)) (as nil (Ref tll_t)) parent lr))
             (= root ll))
        (exists ((l (Ref tll_t)) (r (Ref tll_t)) (z (Ref tll_t)))
            (sep (pto root (tll_cons l r parent (as nil (Ref tll_t))))
                 (tll_plus l root ll z)
                 (tll_plus r root z lr))
        )
    )
)

(declare-const a (Ref tll_t))
(declare-const c (Ref tll_t))

(assert (exists ((l (Ref tll_t)) (r (Ref tll_t)) (z (Ref tll_t)))
            (sep (pto a (tll_cons l r (as nil (Ref tll_t)) (as nil (Ref tll_t))))
                 (tll_plus l a c z)
                 (tll_plus r a z (as nil (Ref tll_t))))
        )
)
(assert (not (tll_plus a (as nil (Ref tll_t)) c (as nil (Ref tll_t)))))

(check-sat)