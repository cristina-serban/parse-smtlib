(set-logic SL)

(declare-datatype dll_t ((empty) (dll_cons (next (Ref dll_t)) (prev (Ref dll_t)))))

(declare-datatype tll_t ((empty) (tll_cons (left (Ref tll_t)) (right (Ref tll_t))
								 		   (parent (Ref tll_t)) (next (Ref tll_t)))))

(define-fun-rec dllseg ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
	(or (and emp (= hd nx) (= pr tl))
		(exists ((x (Ref dll_t))) (sep (pto hd (dll_cons x pr)) (dllseg x hd tl nx))))
)

(define-fun-rec dllseg_rev ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
	(or (and emp (= hd nx) (= pr tl))
		(exists ((x (Ref dll_t))) (sep (pto tl (dll_cons nx x)) (dllseg_rev hd pr x tl)))
	)
)

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