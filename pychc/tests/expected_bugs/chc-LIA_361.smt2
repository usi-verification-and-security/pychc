; ./seahorn/./sv_comp_flat_small/recursive-simple/fibo_25_true-unreach-call.c.flat_000.smt2
(set-logic HORN)

(declare-fun |fibo| ( Bool Bool Bool Int Int ) Bool)
(declare-fun |main_1| ( Int ) Bool)
(declare-fun |fibo_1| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 true) (= v_3 true) (= v_4 true))
      )
      (fibo v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 true) (= v_4 true))
      )
      (fibo v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 false) (= v_4 false))
      )
      (fibo v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and true (= 0 v_2))
      )
      (fibo_1 v_2 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Int) (Q Bool) (R Bool) (S Bool) (T Int) (U Int) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (v_28 Int) (v_29 Bool) (v_30 Bool) (v_31 Bool) (v_32 Bool) (v_33 Int) ) 
    (=>
      (and
        (fibo_1 v_28 J I)
        (fibo N v_29 v_30 A B)
        (fibo N v_31 v_32 C D)
        (and (= 0 v_28)
     (= v_29 false)
     (= v_30 false)
     (= v_31 false)
     (= v_32 false)
     (or (and Q W) (and N X) (not V))
     (or (and L R) (and K S) (not Q))
     (or (= Z Y) (not Q) (not W))
     (or (= Y H) (not Q) (not W))
     (or (= Z E) (not N) (not X))
     (or (= E P) (not N) (not X))
     (or (= T 1) (not L) (not R))
     (or (= H T) (not L) (not R))
     (or (= U 0) (not K) (not S))
     (or (= H U) (not K) (not S))
     (or G (not K) (not S))
     (or (not G) (not K) (not M))
     (or F (not L) (not R))
     (or (not F) (not L) (not O))
     (or (not A1) (and V B1))
     (or (not N) (= P (+ D B)))
     (or (not N) (= C (+ (- 2) I)))
     (or (not N) (= A (+ (- 1) I)))
     (or (not N) (and L O))
     (or (not L) (= F (= I 1)))
     (or (not L) (and K M))
     (= A1 true)
     (not (= (<= 1 I) G))
     (= 1 v_33))
      )
      (fibo_1 v_33 Z I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (fibo_1 v_2 B A)
        (and (= 1 v_2) (= v_3 true) (= v_4 false) (= v_5 false))
      )
      (fibo v_3 v_4 v_5 A B)
    )
  )
)
(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (and true (= 0 v_0))
      )
      (main_1 v_0)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (v_5 Int) (v_6 Bool) (v_7 Bool) (v_8 Bool) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (main_1 v_5)
        (fibo v_6 v_7 v_8 v_9 A)
        (and (= 0 v_5)
     (= v_6 true)
     (= v_7 false)
     (= v_8 false)
     (= 25 v_9)
     (or (not D) (and E C))
     (not B)
     (= D true)
     (= B (= A 75025))
     (= 1 v_10))
      )
      (main_1 v_10)
    )
  )
)
(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (main_1 v_0)
        (= 1 v_0)
      )
      false
    )
  )
)

(check-sat)
(get-model)
(exit)
