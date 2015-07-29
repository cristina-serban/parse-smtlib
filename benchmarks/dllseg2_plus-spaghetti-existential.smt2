; Entail LHS(hd0,tl0,hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19,hd20,tl20) |- RHS(hd0,tl0,hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19,hd20,tl20)

; LHS(hd0,tl0,hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19,hd20,tl20) ::= DLL2_plus(hd0,nil,tl0,hd1) * DLL2_plus(hd1,tl0,tl1,hd2) * DLL2_plus(hd2,tl1,tl2,hd3) * DLL2_plus(hd3,tl2,tl3,hd4) * DLL2_plus(hd4,tl3,tl4,hd5) * DLL2_plus(hd5,tl4,tl5,hd6) * DLL2_plus(hd6,tl5,tl6,hd7) * DLL2_plus(hd7,tl6,tl7,hd8) * DLL2_plus(hd8,tl7,tl8,hd9) * DLL2_plus(hd9,tl8,tl9,hd10) * DLL2_plus(hd10,tl9,tl10,hd11) * DLL2_plus(hd11,tl10,tl11,hd12) * DLL2_plus(hd12,tl11,tl12,hd13) * DLL2_plus(hd13,tl12,tl13,hd14) * DLL2_plus(hd14,tl13,tl14,hd15) * DLL2_plus(hd15,tl14,tl15,hd16) * DLL2_plus(hd16,tl15,tl16,hd17) * DLL2_plus(hd17,tl16,tl17,hd18) * DLL2_plus(hd18,tl17,tl18,hd19) * DLL2_plus(hd19,tl18,tl19,hd20) * DLL2_plus(hd20,tl19,tl20,nil)

; RHS(hd0,tl0,hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19,hd20,tl20) ::= \E hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19 . DLL2_plus_rev(hd0,nil,tl0,hd1) * DLL2_plus_rev(hd1,tl0,tl1,hd2) * DLL2_plus_rev(hd2,tl1,tl2,hd3) * DLL2_plus_rev(hd3,tl2,tl3,hd4) * DLL2_plus_rev(hd4,tl3,tl4,hd5) * DLL2_plus_rev(hd5,tl4,tl5,hd6) * DLL2_plus_rev(hd6,tl5,tl6,hd7) * DLL2_plus_rev(hd7,tl6,tl7,hd8) * DLL2_plus_rev(hd8,tl7,tl8,hd9) * DLL2_plus_rev(hd9,tl8,tl9,hd10) * DLL2_plus_rev(hd10,tl9,tl10,hd11) * DLL2_plus_rev(hd11,tl10,tl11,hd12) * DLL2_plus_rev(hd12,tl11,tl12,hd13) * DLL2_plus_rev(hd13,tl12,tl13,hd14) * DLL2_plus_rev(hd14,tl13,tl14,hd15) * DLL2_plus_rev(hd15,tl14,tl15,hd16) * DLL2_plus_rev(hd16,tl15,tl16,hd17) * DLL2_plus_rev(hd17,tl16,tl17,hd18) * DLL2_plus_rev(hd18,tl17,tl18,hd19) * DLL2_plus_rev(hd19,tl18,tl19,hd20) * DLL2_plus_rev(hd20,tl19,tl20,nil)

; DLL1_plus(hd,p) ::=  hd->nil,p |
;   \E x . hd->x,p * DLL1_plus(x,hd)

; DLL2_plus(hd,p,tl,n) ::=  \E down_hd . hd->n,p,down_hd & hd=tl * DLL1_plus(down_hd,hd) |
;   \E x,down_hd . hd->x,p,down_hd * DLL1_plus(down_hd,hd) * DLL2_plus(x,hd,tl,n)

; DLL2_plus_rev(hd,p,tl,n) ::=  \E down_hd . hd->n,p,down_hd & hd=tl * DLL1_plus(down_hd,hd) |
;   \E x,down_hd . tl->n,x,down_hd * DLL1_plus(down_hd,tl) * DLL2_plus_rev(hd,p,x,tl)

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

(declare-const hd0 (Ref dll2_t))
(declare-const tl0 (Ref dll2_t))
(declare-const hd1 (Ref dll2_t))
(declare-const tl1 (Ref dll2_t))
(declare-const hd2 (Ref dll2_t))
(declare-const tl2 (Ref dll2_t))
(declare-const hd3 (Ref dll2_t))
(declare-const tl3 (Ref dll2_t))
(declare-const hd4 (Ref dll2_t))
(declare-const tl4 (Ref dll2_t))
(declare-const hd5 (Ref dll2_t))
(declare-const tl5 (Ref dll2_t))
(declare-const hd6 (Ref dll2_t))
(declare-const tl6 (Ref dll2_t))
(declare-const hd7 (Ref dll2_t))
(declare-const tl7 (Ref dll2_t))
(declare-const hd8 (Ref dll2_t))
(declare-const tl8 (Ref dll2_t))
(declare-const hd9 (Ref dll2_t))
(declare-const tl9 (Ref dll2_t))
(declare-const hd10 (Ref dll2_t))
(declare-const tl10 (Ref dll2_t))
(declare-const hd11 (Ref dll2_t))
(declare-const tl11 (Ref dll2_t))
(declare-const hd12 (Ref dll2_t))
(declare-const tl12 (Ref dll2_t))
(declare-const hd13 (Ref dll2_t))
(declare-const tl13 (Ref dll2_t))
(declare-const hd14 (Ref dll2_t))
(declare-const tl14 (Ref dll2_t))
(declare-const hd15 (Ref dll2_t))
(declare-const tl15 (Ref dll2_t))
(declare-const hd16 (Ref dll2_t))
(declare-const tl16 (Ref dll2_t))
(declare-const hd17 (Ref dll2_t))
(declare-const tl17 (Ref dll2_t))
(declare-const hd18 (Ref dll2_t))
(declare-const tl18 (Ref dll2_t))
(declare-const hd19 (Ref dll2_t))
(declare-const tl19 (Ref dll2_t))
(declare-const hd20 (Ref dll2_t))
(declare-const tl20 (Ref dll2_t))

(assert (sep (dllseg2_plus hd0 (as nil (Ref dll2_t)) tl0 hd1)
		     (dllseg2_plus hd1 hd0 tl1 hd2)
		     (dllseg2_plus hd2 hd1 tl2 hd3)
		     (dllseg2_plus hd3 hd2 tl3 hd4)
		     (dllseg2_plus hd4 hd3 tl4 hd5)
		     (dllseg2_plus hd5 hd4 tl5 hd6)
		     (dllseg2_plus hd6 hd5 tl6 hd7)
		     (dllseg2_plus hd7 hd6 tl7 hd8)
		     (dllseg2_plus hd8 hd7 tl8 hd9)
		     (dllseg2_plus hd9 hd8 tl9 hd10)
		     (dllseg2_plus hd10 hd9 tl10 hd11)
		     (dllseg2_plus hd11 hd10 tl11 hd12)
		     (dllseg2_plus hd12 hd11 tl12 hd13)
		     (dllseg2_plus hd13 hd12 tl13 hd14)
		     (dllseg2_plus hd14 hd13 tl14 hd15)
		     (dllseg2_plus hd15 hd14 tl15 hd16)
		     (dllseg2_plus hd16 hd15 tl16 hd17)
		     (dllseg2_plus hd17 hd16 tl17 hd18)
		     (dllseg2_plus hd18 hd17 tl18 hd19)
		     (dllseg2_plus hd19 hd18 tl19 hd20)
		     (dllseg2_plus hd20 hd19 tl20 (as nil (Ref dll2_t)))
		)		
)

(assert (not (exists ((hd1 (Ref dll2_t)) (tl1 (Ref dll2_t))
					  (hd2 (Ref dll2_t)) (tl2 (Ref dll2_t))
					  (hd3 (Ref dll2_t)) (tl3 (Ref dll2_t))
					  (hd4 (Ref dll2_t)) (tl4 (Ref dll2_t))
					  (hd5 (Ref dll2_t)) (tl5 (Ref dll2_t))
					  (hd6 (Ref dll2_t)) (tl6 (Ref dll2_t))
					  (hd7 (Ref dll2_t)) (tl7 (Ref dll2_t))
					  (hd8 (Ref dll2_t)) (tl8 (Ref dll2_t))
					  (hd9 (Ref dll2_t)) (tl9 (Ref dll2_t))
					  (hd10 (Ref dll2_t)) (tl10 (Ref dll2_t))
					  (hd11 (Ref dll2_t)) (tl11 (Ref dll2_t))
					  (hd12 (Ref dll2_t)) (tl12 (Ref dll2_t))
					  (hd13 (Ref dll2_t)) (tl13 (Ref dll2_t))
					  (hd14 (Ref dll2_t)) (tl14 (Ref dll2_t))
					  (hd15 (Ref dll2_t)) (tl15 (Ref dll2_t))
					  (hd16 (Ref dll2_t)) (tl16 (Ref dll2_t))
					  (hd17 (Ref dll2_t)) (tl17 (Ref dll2_t))
					  (hd18 (Ref dll2_t)) (tl18 (Ref dll2_t))
					  (hd19 (Ref dll2_t)) (tl19 (Ref dll2_t)))
				(sep (dllseg2_plus_rev hd0 (as nil (Ref dll2_t)) tl0 hd1)
				     (dllseg2_plus_rev hd1 hd0 tl1 hd2)
				     (dllseg2_plus_rev hd2 hd1 tl2 hd3)
				     (dllseg2_plus_rev hd3 hd2 tl3 hd4)
				     (dllseg2_plus_rev hd4 hd3 tl4 hd5)
				     (dllseg2_plus_rev hd5 hd4 tl5 hd6)
				     (dllseg2_plus_rev hd6 hd5 tl6 hd7)
				     (dllseg2_plus_rev hd7 hd6 tl7 hd8)
				     (dllseg2_plus_rev hd8 hd7 tl8 hd9)
				     (dllseg2_plus_rev hd9 hd8 tl9 hd10)
				     (dllseg2_plus_rev hd10 hd9 tl10 hd11)
				     (dllseg2_plus_rev hd11 hd10 tl11 hd12)
				     (dllseg2_plus_rev hd12 hd11 tl12 hd13)
				     (dllseg2_plus_rev hd13 hd12 tl13 hd14)
				     (dllseg2_plus_rev hd14 hd13 tl14 hd15)
				     (dllseg2_plus_rev hd15 hd14 tl15 hd16)
				     (dllseg2_plus_rev hd16 hd15 tl16 hd17)
				     (dllseg2_plus_rev hd17 hd16 tl17 hd18)
				     (dllseg2_plus_rev hd18 hd17 tl18 hd19)
				     (dllseg2_plus_rev hd19 hd18 tl19 hd20)
				     (dllseg2_plus_rev hd20 hd19 tl20 (as nil (Ref dll2_t))))				 
			 )
		)
)

(check-sat)