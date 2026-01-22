
(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-fun K () Int)
(declare-fun P () Int)
(declare-fun R () Int)
(declare-fun X () Int)
(declare-fun Z () Int)

(assert (let ((.def_0 (= 0 Z))) (let ((.def_1 (< 0 X))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= 1 Z))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (<= 1 R))) (let ((.def_6 (<= 0 K))) (let ((.def_7 (<= 1 P))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (= 0 X))) (let ((.def_10 (not .def_0))) (let ((.def_11 (and .def_10 .def_0))) (let ((.def_12 (not .def_8))) (let ((.def_13 (or .def_12 .def_11 .def_9))) (let ((.def_14 (and .def_13 .def_8 .def_4 .def_2))) .def_14))))))))))))))))

(check-sat)
(get-proof)