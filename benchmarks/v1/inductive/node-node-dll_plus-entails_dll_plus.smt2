(set-logic SEPLOG)

(declare-sort Ref 1)

(declare-datatype dll_t ((empty) (dll_cons (next (Ref dll_t)) (prev (Ref dll_t)))))

(define-fun-rec dllseg_plus ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
    (or (and (pto hd (dll_cons nx pr)) (= hd tl))
        (exists ((x (Ref dll_t))) (sep (pto hd (dll_cons x pr)) (dllseg_plus x hd tl nx))))
)

(declare-const x (Ref dll_t))
(declare-const c (Ref dll_t))

(assert (exists ((y (Ref dll_t)) (a (Ref dll_t))) 
            (sep (pto x (dll_cons y (as nil (Ref dll_t))))
                 (pto y (dll_cons a x))
                 (dllseg_plus a y c (as nil (Ref dll_t))))
        )
)
(assert (not (dllseg_plus x (as nil (Ref dll_t)) c (as nil (Ref dll_t)))))

(check-sat)