(set-logic HORN)
(declare-fun inv (Int) Bool)

(assert (=> true (inv 0)))
(assert (forall ((x Int)) (=> (and (inv x) (= x 0)) false)))

(check-sat)
