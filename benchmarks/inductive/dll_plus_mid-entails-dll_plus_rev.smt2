; Entail LHS(x,y) |- RHS(x,y)

; LHS(x,y) ::= DLL_plus_mid(x,nil,y,nil)

; RHS(x,y) ::= DLL_plus_rev(x,nil,y,nil)

; points_to(a,b,c) ::=  a->b,c

; DLL_plus(hd,p,tl,n) ::=  hd->n,p & hd=tl |
;  \E x . hd->x,p * DLL_plus(x,hd,tl,n)

; DLL_plus_rev(hd,p,tl,n) ::=  hd->n,p & hd=tl |
;   \E x . tl->n,x * DLL_plus_rev(hd,p,x,tl)

; DLL_plus_mid(hd,p,tl,n) ::=  hd->n,p & hd=tl |
;   hd->tl,p * points_to(tl,n,hd) |
;   \E x,y,z . x->y,z * DLL_plus(y,x,tl,n) * DLL_plus_rev(hd,p,z,x)

  (set-logic SL)

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

(define-fun-rec dllseg_plus_mid ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
	(or (and (pto hd (dll_cons nx pr)) (= hd tl))
		(or (sep (pto hd (dll_cons tl pr)) (pto tl (dll_cons nx hd)))
			(exists ((x (Ref dll_t)) (y (Ref dll_t)) (z (Ref dll_t))) 
				(sep (pto x (dll_cons y z)) (dllseg_plus y x tl nx) (dllseg_plus_rev hd pr z nx))
			) 
		)
	)
)

(declare-const x (Ref dll_t))
(declare-const y (Ref dll_t))

(assert (dllseg_plus_mid x (as nil (Ref dll_t)) y (as nil (Ref dll_t))))
(assert (not (dllseg_plus_rev x (as nil (Ref dll_t)) y (as nil (Ref dll_t)))))

(check-sat)