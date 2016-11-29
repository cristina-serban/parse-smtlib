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

(define-fun-rec tll_tail ((root (Ref tll_t)) (parent (Ref tll_t)) (ll (Ref tll_t)) (tr (Ref tll_t)) (lr (Ref tll_t))) Bool
    (or (and (pto root (tll_cons (as nil (Ref tll_t)) (as nil (Ref tll_t)) parent lr))
             (= root ll)
             (= root tr))
        (exists ((l (Ref tll_t)) (r (Ref tll_t)) (z (Ref tll_t)))
            (sep (pto root (tll_cons l r parent (as nil (Ref tll_t))))
                 (tll_plus l root ll z)
                 (tll_tail r root z tr lr))
        )
    )
)

(declare-const root0 (Ref tll_t)) (declare-const ll0 (Ref tll_t)) (declare-const tr0 (Ref tll_t))
(declare-const root1 (Ref tll_t)) (declare-const ll1 (Ref tll_t)) (declare-const tr1 (Ref tll_t))
(declare-const root2 (Ref tll_t)) (declare-const ll2 (Ref tll_t)) (declare-const tr2 (Ref tll_t))
(declare-const root3 (Ref tll_t)) (declare-const ll3 (Ref tll_t)) (declare-const tr3 (Ref tll_t))
(declare-const root4 (Ref tll_t)) (declare-const ll4 (Ref tll_t)) (declare-const tr4 (Ref tll_t))
(declare-const root5 (Ref tll_t)) (declare-const ll5 (Ref tll_t)) (declare-const tr5 (Ref tll_t))
(declare-const root6 (Ref tll_t)) (declare-const ll6 (Ref tll_t)) (declare-const tr6 (Ref tll_t))
(declare-const root7 (Ref tll_t)) (declare-const ll7 (Ref tll_t)) (declare-const tr7 (Ref tll_t))
(declare-const root8 (Ref tll_t)) (declare-const ll8 (Ref tll_t)) (declare-const tr8 (Ref tll_t))
(declare-const root9 (Ref tll_t)) (declare-const ll9 (Ref tll_t)) (declare-const tr9 (Ref tll_t))
(declare-const root10 (Ref tll_t)) (declare-const ll10 (Ref tll_t)) (declare-const tr10 (Ref tll_t))
(declare-const root11 (Ref tll_t)) (declare-const ll11 (Ref tll_t)) (declare-const tr11 (Ref tll_t))
(declare-const root12 (Ref tll_t)) (declare-const ll12 (Ref tll_t)) (declare-const tr12 (Ref tll_t))
(declare-const root13 (Ref tll_t)) (declare-const ll13 (Ref tll_t)) (declare-const tr13 (Ref tll_t))
(declare-const root14 (Ref tll_t)) (declare-const ll14 (Ref tll_t)) (declare-const tr14 (Ref tll_t))
(declare-const root15 (Ref tll_t)) (declare-const ll15 (Ref tll_t)) (declare-const tr15 (Ref tll_t))
(declare-const root16 (Ref tll_t)) (declare-const ll16 (Ref tll_t)) (declare-const tr16 (Ref tll_t))
(declare-const root17 (Ref tll_t)) (declare-const ll17 (Ref tll_t)) (declare-const tr17 (Ref tll_t))
(declare-const root18 (Ref tll_t)) (declare-const ll18 (Ref tll_t)) (declare-const tr18 (Ref tll_t))
(declare-const root19 (Ref tll_t)) (declare-const ll19 (Ref tll_t)) (declare-const tr19 (Ref tll_t))

(assert (sep (tll_tail root0 (as nil (Ref tll_t)) ll0 tr0 root1)
             (tll_tail root1 tr0 ll1 tr1 root2)
             (tll_tail root2 tr1 ll2 tr2 root3)
             (tll_tail root3 tr2 ll3 tr3 root4)
             (tll_tail root4 tr3 ll4 tr4 root5)
             (tll_tail root5 tr4 ll5 tr5 root6)
             (tll_tail root6 tr5 ll6 tr6 root7)
             (tll_tail root7 tr6 ll7 tr7 root8)
             (tll_tail root8 tr7 ll8 tr8 root9)
             (tll_tail root9 tr8 ll9 tr9 root10)
             (tll_tail root10 tr9 ll10 tr10 root11)
             (tll_tail root11 tr10 ll11 tr11 root12)
             (tll_tail root12 tr11 ll12 tr12 root13)
             (tll_tail root13 tr12 ll13 tr13 root14)
             (tll_tail root14 tr13 ll14 tr14 root15)
             (tll_tail root15 tr14 ll15 tr15 root16)
             (tll_tail root16 tr15 ll16 tr16 root17)
             (tll_tail root17 tr16 ll17 tr17 root18)
             (tll_tail root18 tr17 ll18 tr18 root19)
             (tll_tail root19 tr18 ll19 tr19 (as nil (Ref tll_t)))
        )
)

(assert (not (sep (tll_tail root0 (as nil (Ref tll_t)) ll0 tr0 root1)
                  (tll_tail root2 tr1 ll2 tr2 root3)
                  (tll_tail root5 tr4 ll5 tr5 root6)
                  (tll_tail root8 tr7 ll8 tr8 root9)
                  (tll_tail root10 tr9 ll10 tr10 root11)
                  (tll_tail root7 tr6 ll7 tr7 root8)
                  (tll_tail root9 tr8 ll9 tr9 root10)
                  (tll_tail root4 tr3 ll4 tr4 root5)
                  (tll_tail root13 tr12 ll13 tr13 root14)
                  (tll_tail root11 tr10 ll11 tr11 root12)
                  (tll_tail root15 tr14 ll15 tr15 root16)
                  (tll_tail root12 tr11 ll12 tr12 root13)
                  (tll_tail root17 tr16 ll17 tr17 root18)
                  (tll_tail root14 tr13 ll14 tr14 root15)
                  (tll_tail root6 tr5 ll6 tr6 root7)
                  (tll_tail root19 tr18 ll19 tr19 (as nil (Ref tll_t)))
                  (tll_tail root1 tr0 ll1 tr1 root2)
                  (tll_tail root16 tr15 ll16 tr16 root17)
                  (tll_tail root3 tr2 ll3 tr3 root4)
                  (tll_tail root18 tr17 ll18 tr18 root19))
        )
)

(check-sat)