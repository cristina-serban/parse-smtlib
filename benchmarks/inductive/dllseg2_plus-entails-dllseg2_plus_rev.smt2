; Entail LHS(x,y,u,v) |- RHS(x,y,u,v)
; LHS(x,y,u,v) ::= DLL2_plus(x,y,u,v)
; RHS(x,y,u,v) ::= DLL2_plus_rev(x,y,u,v)

; DLL1_plus(hd,p) ::=  hd->nil,p |
;  \E x . hd->x,p * DLL1_plus(x,hd)

; DLL2_plus(hd,p,tl,n) ::=  \E down_hd . hd->n,p,down_hd & hd=tl * DLL1_plus(down_hd,hd) |
;  \E x,down_hd . hd->x,p,down_hd * DLL1_plus(down_hd,hd) * DLL2_plus(x,hd,tl,n)

; DLL2_plus_rev(hd,p,tl,n) ::=  \E down_hd . hd->n,p,down_hd & hd=tl * DLL1_plus(down_hd,hd) |
;  \E x,down_hd . tl->n,x,down_hd * DLL1_plus(down_hd,tl) * DLL2_plus_rev(hd,p,x,tl)

(set-logic SL)

(declare-datatype dll1_t ((empty) (dll1_cons (next (Ref dll1_t)) (prev (Ref dll1_t)))))

(declare-datatype dll2_t ((empty) (dll2_cons (next (Ref dll2_t)) (prev (Ref dll2_t)) (down (Ref dll1_t)))))

(define-fun-rec dll1_plus ((hd (Ref dll1_t)) (pr (Ref dll1_t))) Bool
	(or (pto hd (dll1_cons (as nil (Ref dll1_t)) pr))
		(exists ((x (Ref dll1_t))) (sep (pto hd (dll1_cons x pr)) (dll1_plus x hd))))
)

(define-fun-rec dllseg2_plus ((hd (Ref dll2_t)) (pr (Ref dll2_t)) 
							  (tl (Ref dll2_t)) (nx (Ref dll2_t))) Bool
	(or (exists ((down_hd (Ref dll1_t))) 
			(and (= hd tl) 
				 (sep (pto hd (dll2_cons nx pr down_hd)) 
					  (dll1_plus down_hd (as nil (Ref dll1_t))))))
		(exists ((x (Ref dll2_t)) (down_hd (Ref dll1_t))) 
			(sep (pto hd (dll2_cons x pr down_hd)) 
				 (dll1_plus down_hd (as nil (Ref dll1_t))) 
				 (dllseg2_plus x hd tl nx))))
)

(define-fun-rec dllseg2_plus_rev ((hd (Ref dll2_t)) (pr (Ref dll2_t)) 
								  (tl (Ref dll2_t)) (nx (Ref dll2_t))) Bool
	(or (exists ((down_hd (Ref dll1_t))) 
			(and (= hd tl) 
				 (sep (pto hd (dll2_cons nx pr down_hd)) 
					  (dll1_plus down_hd (as nil (Ref dll1_t))))))
		(exists ((x (Ref dll2_t)) (down_hd (Ref dll1_t))) 
			(sep (pto tl (dll2_cons nx x down_hd)) 
				 (dll1_plus down_hd (as nil (Ref dll1_t))) 
				 (dllseg2_plus_rev hd pr x tl))))
)

(declare-const x (Ref dll2_t))
(declare-const y (Ref dll2_t))
(declare-const u (Ref dll2_t))
(declare-const v (Ref dll2_t))

(assert (dllseg2_plus x y u v))
(assert (not (dllseg2_plus_rev x y u v)))

(check-sat)