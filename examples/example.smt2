;; chc-comp25-benchmarks/eldarica-misc/LIA/HOLA/30.c_000.yml

(set-logic HORN)

(declare-fun |h1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h3| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h4| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h5| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h6| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h7| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h8| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h9| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h10| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h11| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h12| ( Int Int Int Int Int Int ) Bool)
(declare-fun |h13| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and true (= v_3 A) (= v_4 B) (= v_5 C))
      )
      (h1 A B C v_3 v_4 v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h1 A B C G H F)
        (and (= D 0) (= E 0))
      )
      (h2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h2 A B C D E F)
        true
      )
      (h3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h3 A B C D E F)
        true
      )
      (h4 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h4 A B C D E F)
        true
      )
      (h5 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h8 A B C D E F)
        true
      )
      (h5 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h5 A B C D E F)
        true
      )
      (h6 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h6 A B C D E F)
        (<= D 999)
      )
      (h7 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h7 A B C H G F)
        (and (= G (+ 1 (* (- 1) D) E)) (= H (+ (- 1) D)))
      )
      (h8 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h6 A B C D E F)
        (>= D 1000)
      )
      (h9 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h9 A B C D E F)
        true
      )
      (h10 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h10 A B C D E F)
        true
      )
      (h11 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h11 A B C D E F)
        true
      )
      (h12 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h12 A B C D E F)
        (<= E (- 1))
      )
      (h13 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (h13 A B C D E F)
        true
      )
      false
    )
  )
)

(check-sat)
(get-model)
(exit)
