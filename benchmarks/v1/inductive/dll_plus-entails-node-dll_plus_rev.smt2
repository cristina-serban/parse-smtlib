(set-logic SEPLOG)

(declare-sort Ref 1)

(declare-datatype dll_t ((empty) (dll_cons (next (Ref dll_t)) (prev (Ref dll_t)))))

(define-fun-rec dllseg_plus ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
    (or (and (pto hd (dll_cons nx pr)) (= hd tl))
        (exists ((x (Ref dll_t))) (sep (pto hd (dll_cons x pr)) (dllseg_plus x hd tl nx))))
)

(define-fun-rec dllseg_plus_rev ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
    (or (and (pto hd (dll_cons nx pr)) (= hd tl))
        (exists ((x (Ref dll_t))) (sep (pto tl (dll_cons nx x)) (dllseg_plus_rev hd pr x tl)))
    )
)

(declare-const a (Ref dll_t))
(declare-const c (Ref dll_t))

(assert (dllseg_plus a (as nil (Ref dll_t)) c (as nil (Ref dll_t))))

(assert (not (exists ((x (Ref dll_t)) (n (Ref dll_t)) (b (Ref dll_t))) 
                (sep (pto x (dll_cons n b))
                     (dllseg_plus_rev a (as nil (Ref dll_t)) b x)
                     (dllseg_plus n x c (as nil (Ref dll_t))))
             )
        )
)

(check-sat)