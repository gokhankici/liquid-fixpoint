// TODO move to actual SMTLIB format 
(fixpoint "--eliminate=horn")

(var $k0 ((x Int)))

(qualif Foo ((v Int)) ((v > 100)))

(constraint 
  (forall ((x Int) (x > 0))
    (and
      (forall ((y Int) (y > x + 100))
        (forall ((v Int) (v = x + y)) 
          (($k0 v))))
      (forall ((z Int) ($k0 z))
        (forall ((v Int) (v = x + z)) 
          ((v > 100)))))))


