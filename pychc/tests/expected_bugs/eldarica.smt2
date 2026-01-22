;; https://github.com/uuverifiers/eldarica/issues/51

(set-logic HORN)

(declare-fun |state| ( Bool Bool Bool Bool Int Int Int ) Bool)

(assert (forall ((C Int) (D Int) (E Int)) (state false true false false C D E)))

(assert (forall ((A Bool)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Int)
         (H Int)
         (I Int)
         (J Int)
         (K Int)
         (L Int)
         (M Bool)
         (N Bool))
  (let ((a!1 (and (state B A N M H J L)
                  (or M N (not A) (not B) (and F D (not C) (= H G)))
                  (or M A B)
                  (or M (not N) A)
                  (or N (not M) (not B))
                  (or M N B (and (not F) E (not D) (= G 1)))
                  (or M N A (and E D (not C) (= H G)))
                  (or N B (<= H 0)))))
    (or (not a!1) (state E D C F G I K)))))
    
(assert (forall ((C Int) (D Int) (E Int)) (not (state false false true true C D E))))

(check-sat)