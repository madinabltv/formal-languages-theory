(set-logic QF_NIA)

(declare-const g1 Int)
(assert (>=  g1 1))
(declare-const g2 Int)
(assert (>=  g2 1))
(declare-const g3 Int)
(assert (>=  g3 0))
(assert (or (and(> g1 1) (> g2 1)) (> g3 0)))

(declare-const f1 Int)
(assert (>=  f1 1))
(declare-const f2 Int)
(assert (>=  f2 0))
(assert (or (and(> f1 1)) (> f2 0)))

(declare-const h1 Int)
(assert (>=  h1 1))
(declare-const h2 Int)
(assert (>=  h2 0))
(assert (or (and(> h1 1)) (> h2 0)))


(assert (or 
    (and
        (>= (+ (* 1 g2 f1)) (+ (* 1 h1 g1)))  ; y
        (> (+ (* f2) (* g3 f1)) (+ (* g3) (* h2 g1)))  ; id
        (>= (+ (* 1 g1 f1)) (+ (* 1 g2)))  ; x
    )
    (and
        (> (+ (* 1 g2 f1)) (+ (* 1 h1 g1)))  ; y
        (>= (+ (* f2) (* g3 f1)) (+ (* g3) (* h2 g1)))  ; id
        (> (+ (* 1 g1 f1)) (+ (* 1 g2)))  ; x
    )
))
(assert (or 
    (and
        (>= (+ (* 1 f1 h1)) (+ (* 1 f1)))  ; x
        (> (+ (* h2) (* f2 h1)) (+ (* f2)))  ; id
    )
    (and
        (> (+ (* 1 f1 h1)) (+ (* 1 f1)))  ; x
        (>= (+ (* h2) (* f2 h1)) (+ (* f2)))  ; id
    )
))

(check-sat)
