(set-logic HORN)
(set-info :status unsat) ;; this means invalid, i.e. buggy

(declare-fun p (Int) Bool)

(assert
 (forall
  ((A Int) (B Int))
  (=>
   (= A 1)
   (p A)
   )))

(assert
 (forall
  ((A Int) (B Int) (C Int) (D Int))
  (=>
   (and
    (or
     (and (= C 2) (= B C) (= A 3))
     (and (= C 1) (= B C) (= A 4))
     )
    (p B))
   (p A))))

;; invalid
 (assert
  (not
   (exists
    ((A Int) (B Int))
    (and (= B A)  (not (< B 4)) (p A))
    )))

;; valid
 (assert
  (not
   (exists
    ((A Int))
    (and (> A 5) (p A))
    )))

(check-sat)
