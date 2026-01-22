  (define-fun main_1 ((x!0 Int) (x!1 Int) (x!2 Int) (x!3 Int) (x!4 Int)) Bool
    (and (or (not (<= x!4 5)) (not (>= x!0 1)))
         (or (not (>= x!0 1)) (not (>= x!3 9)))
         (or (not (>= x!0 1)) (not (>= x!1 2)))
         (or (not (>= x!0 1)) (not (>= x!4 8)) (not (= x!3 7)))
         (or (not (= x!4 9)) (not (>= x!0 1)))
         (or (not (= x!4 8)) (not (>= x!0 1)))
         (or (not (>= x!0 1)) (not (>= x!4 11)))))