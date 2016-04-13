(theory SepLogic

 :sorts ((Ref 1))

 :funs ((emp Bool)
        (sep Bool Bool Bool :left-assoc)
        (par (A B) (pto A B Bool))
        (par (A) (nil (Ref A)))
       )
)
