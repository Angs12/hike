(declare-const cond Bool)
(declare-const true_addr Int)
(declare-const true_bb Int)
(declare-const false_addr Int)
(declare-const wprime Int)
(declare-const w Int)

(declare-fun JMPS (Int Int) Int)
(assert (not (= true_addr false_addr)))
(assert (not (= true_bb false_addr)))
(assert (not (= true_bb true_addr)))

(assert (forall ((wprime_var Int) (w_var Int)) (= (JMPS w_var wprime_var) wprime_var)))

(declare-fun IF (Int Bool Int Int) Int)
(assert (= (IF w true true_addr false_addr) (JMPS w true_addr)))
(assert (= (IF w false true_addr false_addr) (JMPS w false_addr)))

(declare-fun TRANSFORMED_IF (Int Bool Int Int Int) Int)
(assert (= (TRANSFORMED_IF w true true_addr false_addr true_bb) (JMPS (JMPS w true_bb) true_addr)))
(assert (= (TRANSFORMED_IF w false true_addr false_addr true_bb) (JMPS w false_addr)))

(assert (not (= (TRANSFORMED_IF w cond true_addr false_addr true_bb) (IF w cond true_addr false_addr))))

(check-sat)
(get-model)
