(set-logic SEPLOGLIA)

(declare-sort Loc 0)

(declare-datatype Node ((node (next Loc) (prev Loc))))

(define-fun-rec dllseg ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and emp (= hd nx) (= pr tl))
        (exists ((x Loc)) (sep (pto hd (node x pr)) (dllseg x hd tl nx))))
)

(define-fun-rec dllseg_rev ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and emp (= hd nx) (= pr tl))
        (exists ((x Loc)) (sep (pto tl (node nx x)) (dllseg_rev hd pr x tl)))
    )
)