; Entail LHS(x,y,u,v) |- RHS(x,y,u,v)

; LHS(x,y,u,v) ::= TLL_plus_rev(x,y,u,v)

; RHS(x,y,u,v) ::= TLL_plus(x,y,u,v)

; TLL_plus(root,par,ll,lr) ::=  root->nil,nil,par,lr & root=ll |
;  \E l,r,z . root->l,r,par,nil * TLL_plus(l,root,ll,z) * TLL_plus(r,root,z,lr)

; TLL_aux(x,p,z,back,top,mright) ::=  \E up,r,lr . x->back,r,up,nil * TLL_aux(up,p,lr,x,top,mright) * TLL_plus(r,x,z,lr) |
;   \E r . x->back,r,p,nil & x=top * TLL_plus(r,x,z,mright)

; TLL_plus_rev(top,p,mleft,mright) ::=  top->nil,nil,p,mright & top=mleft |
;   \E x,up,lr . x->nil,nil,up,lr & mleft=x * TLL_aux(up,p,lr,x,top,mright)

(set-logic SL)

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

(define-fun-rec tll_aux ((x (Ref tll_t)) (p (Ref tll_t)) (z (Ref tll_t)) 
						 (back (Ref tll_t)) (top (Ref tll_t)) (mright (Ref tll_t))) Bool
	(or (exists ((up (Ref tll_t)) (r (Ref tll_t)) (lr (Ref tll_t)))
			(sep (pto x (tll_cons back r up (as nil (Ref tll_t)))) 
				 (tll_aux up p lr x top mright) 
				 (tll_plus r x z lr))
		)
		(exists ((r (Ref tll_t))) 
			(and (= x top)
				 (sep (pto x (tll_cons back r p (as nil (Ref tll_t)))) 
				 	  (tll_plus r x z mright))
			)			
		)
	)
)

(define-fun-rec tll_plus_rev ((top (Ref tll_t)) (p (Ref tll_t)) (mleft (Ref tll_t)) (mright (Ref tll_t))) Bool
	(or (and (pto top (tll_cons (as nil (Ref tll_t)) (as nil (Ref tll_t)) p mright)) 
			 (= top mleft))
		(exists ((x (Ref tll_t)) (up (Ref tll_t)) (lr (Ref tll_t))) 
			(and (= mleft x)
				 (sep (pto x (tll_cons (as nil (Ref tll_t)) (as nil (Ref tll_t)) up lr)) 
					  (tll_aux up p lr x top mright))
			)				
		)
	)
)

(declare-const x (Ref tll_t))
(declare-const y (Ref tll_t))
(declare-const u (Ref tll_t))
(declare-const v (Ref tll_t))

(assert (tll_plus_rev x y u v))
(assert (not (tll_plus x y u v)))

(check-sat)