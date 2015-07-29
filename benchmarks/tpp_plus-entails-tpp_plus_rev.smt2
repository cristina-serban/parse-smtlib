; Entail LHS(x,y) |- RHS(x,y)

; LHS(x,y) ::= TPP_plus(x,y)

; RHS(x,y) ::= TPP_plus_rev(x,y)

; TPP_plus(x,back) ::=  x->nil,nil,back |
;   \E y,z . x->y,z,back * TPP_plus(y,x) * TPP_plus(z,x)

; TPP_aux(x,down,top,b) ::=  \E up,right . x->down,right,up * TPP_plus(right,x) * TPP_aux(up,x,top,b) |
;   \E up,left . x->left,down,up * TPP_plus(left,x) * TPP_aux(up,x,top,b) |
;   \E right . x->down,right,b & x=top * TPP_plus(right,x) |
;   \E left . x->left,down,b & x=top * TPP_plus(left,x)

; TPP_plus_rev(top,b) ::=  top->nil,nil,b |
;   \E x,up . x->nil,nil,up * TPP_aux(up,x,top,b)

(set-logic SL)

(declare-datatype tpp_t ((empty) (tpp_cons (left (Ref tpp_t)) (right (Ref tpp_t)) (parent (Ref tpp_t)))))

(define-fun-rec tpp_plus ((x (Ref tpp_t)) (back (Ref tpp_t))) Bool
	(or (pto x (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) back)) 
		(exists ((y (Ref tpp_t)) (z (Ref tpp_t))) 
			(sep (pto x (tpp_cons y z back)) 
				 (tpp_plus y x)
				 (tpp_plus z x))
		)
	)
)

(define-fun-rec tpp_aux ((x (Ref tpp_t)) (down (Ref tpp_t)) (top (Ref tpp_t)) (b (Ref tpp_t))) Bool
	(or (exists ((up (Ref tpp_t)) (right (Ref tpp_t)))
			(sep (pto x (tpp_cons down right up)) 
				 (tpp_plus right x) 
				 (tpp_aux up x top b))
		)
		(exists ((up (Ref tpp_t)) (left (Ref tpp_t)))
			(sep (pto x (tpp_cons left down up)) 
				 (tpp_plus left x) 
				 (tpp_aux up x top b))
		)
		(exists ((right (Ref tpp_t))) 
			(and (= x top)
				 (sep (pto x (tpp_cons down right b)) 
				 	  (tpp_plus right x))
			)			
		)
		(exists ((left (Ref tpp_t))) 
			(and (= x top)
				 (sep (pto x (tpp_cons left down b)) 
				 	  (tpp_plus left x))
			)			
		)
	)
)

(define-fun-rec tpp_plus_rev ((top (Ref tpp_t)) (b (Ref tpp_t))) Bool
	(or (pto top (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) b))
		(exists ((x (Ref tpp_t)) (up (Ref tpp_t))) 
			(sep (pto x (tpp_cons (as nil (Ref tpp_t)) (as nil (Ref tpp_t)) up)) 
				 (tpp_aux up x top b))
		)
	)
)

(declare-const x (Ref tpp_t))
(declare-const y (Ref tpp_t))

(assert (tpp_plus x y))
(assert (not (tpp_plus_rev x y)))

(check-sat)