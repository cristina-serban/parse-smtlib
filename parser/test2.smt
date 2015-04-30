; This is a basic example that uses comparison
; between integers, push, pop, statistics, and 
; retrieves the current assertions

(set-option :interactive-mode true) ; enable (get-assertions) command
(set-logic QF_LIA)
(declare-fun w () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x y))
(assert (> y z))
(push 1)
(assert (> z x))
(check-sat)
(get-info :all-statistics)
(pop 1)
(push 1)
(assert (= x w))
(check-sat)
(get-assertions)
(exit)
