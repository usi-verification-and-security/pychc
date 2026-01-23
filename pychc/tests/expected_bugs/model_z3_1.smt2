(define-fun main_1 ((x!0 Int) (x!1 Int) (x!2 Int) (x!3 Int)) Bool
    (let ((a!1 (not (>= (+ x!2 (* (- 2) x!3)) (- 1))))
          (a!2 (not (<= (+ x!2 (* (- 2) x!3)) (- 3))))
          (a!3 (not (<= (+ (* 2 x!1) (* (- 1) x!2)) 1)))
          (a!4 (not (= x!2 (+ (- 2) (* 2 x!1))))))
      (or (= x!0 0)
          (and (= x!0 2) a!1 a!2 a!3 (not (= x!2 (- 2))) a!4 (<= x!1 x!3))
          (and a!1 a!2 a!3))))