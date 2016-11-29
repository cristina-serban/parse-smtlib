(theory SepLogic

 :sorts ((Ref 1))

 :funs ((emp Bool)
        (sep Bool Bool Bool :left-assoc)
        (par (A) (pto (Ref A) A Bool))
        (par (A) (nil (Ref A)))
       )
)