; Entail LHS(a,c) |- RHS(a,c)

; LHS(a,c) ::= DLL_plus(a,nil,c,nil)
; RHS(a,c) ::= DLL(a,nil,c,nil)

; DLL(hd,p,tl,n) ::=  p=tl & hd=n & emp |
;  \E x . hd->x,p * DLL(x,hd,tl,n)

; DLL_plus(hd,p,tl,n) ::=  hd->n,p & hd=tl |
;  \E x . hd->x,p * DLL_plus(x,hd,tl,n)

(set-logic SL)

(declare-datatype dll_t ((empty) (dll_cons (next (Ref dll_t)) (prev (Ref dll_t)))))

(define-fun-rec dllseg ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
	(or (and emp (= hd nx) (= pr tl))
		(exists ((x (Ref dll_t))) (sep (pto hd (dll_cons x pr)) (dllseg x hd tl nx))))
)

(define-fun-rec dllseg_plus ((hd (Ref dll_t)) (pr (Ref dll_t)) (tl (Ref dll_t)) (nx (Ref dll_t))) Bool
	(or (and (pto hd (dll_cons nx pr)) (= hd tl)) 
		(exists ((x (Ref dll_t))) (sep (pto hd (dll_cons x pr)) (dllseg_plus x hd tl nx))))
)

(declare-const x (Ref dll_t))
(declare-const y (Ref dll_t))

(assert (dllseg_plus x (as nil (Ref dll_t)) y (as nil (Ref dll_t))))
(assert (not (dllseg x (as nil (Ref dll_t)) y (as nil (Ref dll_t)))))

(check-sat)