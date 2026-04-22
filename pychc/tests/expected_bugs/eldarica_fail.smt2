(set-logic HORN)


(declare-fun |%main.17| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.25| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.29| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.37| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.13| ( Int Int Bool Bool ) Bool)
(declare-fun |%main| ( Bool ) Bool)
(declare-fun |%main.1| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.9| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.21| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.33| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.40| ( Int Int Bool Bool ) Bool)
(declare-fun |%main.5| ( Int Int Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (%main.1 v_2 v_3 B A)
        (and (= 1 v_2) (= 1 v_3))
      )
      (%main A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.5 A B D C)
        (= v_4 false)
      )
      (%main.1 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.5 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.1 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.9 A B D C)
        (= v_4 false)
      )
      (%main.5 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.9 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.5 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.13 A B D C)
        (= v_4 false)
      )
      (%main.9 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.13 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.9 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.17 A B D C)
        (= v_4 false)
      )
      (%main.13 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.17 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.13 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.21 A B D C)
        (= v_4 false)
      )
      (%main.17 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.21 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.17 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.25 A B D C)
        (= v_4 false)
      )
      (%main.21 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.25 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.21 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.29 A B D C)
        (= v_4 false)
      )
      (%main.25 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.29 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.25 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.33 A B D C)
        (= v_4 false)
      )
      (%main.29 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.33 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.29 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.37 A B D C)
        (= v_4 false)
      )
      (%main.33 A B v_4 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.37 B A F E)
        (and (= B (+ 1 C)) (= A (+ 1 D)) (= v_6 true))
      )
      (%main.33 C D v_6 E)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Bool) (v_4 Bool) ) 
    (=>
      (and
        (%main.40 B C A D)
        (and (not (= (<= B 11) A)) (= v_4 false))
      )
      (%main.37 B C v_4 D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool) (v_6 Bool) ) 
    (=>
      (and
        (%main.40 C B A F)
        (and (= C (+ 1 D)) (not (= (<= D 10) A)) (= B (+ 1 E)) (= v_6 true))
      )
      (%main.37 D E v_6 F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (v_3 Bool) ) 
    (=>
      (and
        (and (not C) (= v_3 false))
      )
      (%main.40 A B v_3 C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (v_3 Bool) ) 
    (=>
      (and
        (and (= C true) (= v_3 true))
      )
      (%main.40 A B v_3 C)
    )
  )
)
(assert
  (forall ( (v_0 Bool) ) 
    (=>
      (and
        (%main v_0)
        (= v_0 true)
      )
      false
    )
  )
)

(check-sat)
(exit)
