;; hack: putting all the constants we might need here
;; rather than trying to produce exactly the ones we need
(declare-const _0 Int)
(declare-const _1 Int)

(declare-const c0 Int)
(declare-const c1 Int)

(declare-fun max (Int Int) Int)
(declare-fun min (Int Int) Int)

(assert (>= (max _0 _1) _0))
(assert (>= (max _0 _1) _1))
(assert (or (= _0 (max _0 _1)) (= _1 (max _0 _1))))
(assert (= (max _0 _1) (max _1 _0)))

(assert (>= (max _0 c0) c0))
(assert (>= (max _0 c0) _0))
(assert (or (= _0 (max _0 c0)) (= c0 (max _0 c0))))
(assert (= (max _0 c0) (max c0 _0)))

(assert (>= (max _0 c1) c1))
(assert (>= (max _0 c1) _0))
(assert (or (= _0 (max _0 c1)) (= c1 (max _0 c1))))
(assert (= (max _0 c1) (max c1 _0)))

(assert (>= (max _1 c0) _1))
(assert (>= (max _1 c0) c0))
(assert (or (= _1 (max _1 c0)) (= c0 (max _1 c0))))
(assert (= (max _1 c0) (max c0 _1)))

(assert (>= (max c0 c1) c0))
(assert (>= (max c0 c1) c1))
(assert (or (= c0 (max c0 c1)) (= c1 (max c0 c1))))
(assert (= (max c0 c1) (max c1 c0)))

(assert (<= (min _0 _1) _0))
(assert (<= (min _0 _1) _1))
(assert (or (= _0 (min _0 _1)) (= _1 (min _0 _1))))
(assert (= (min _0 _1) (min _1 _0)))

(assert (<= (min _0 c0) _0))
(assert (<= (min _0 c0) c0))
(assert (or (= _0 (min _0 c0)) (= c0 (min _0 c0))))
(assert (= (min _0 c0) (min c0 _0)))

(assert (<= (min _0 c1) _0))
(assert (<= (min _0 c1) c1))
(assert (or (= _0 (min _0 c1)) (= c1 (min _0 c1))))
(assert (= (min _0 c1) (min c1 _0)))

(assert (<= (min _1 c0) _1))
(assert (<= (min _1 c0) c0))
(assert (or (= _1 (min _1 c0)) (= c0 (min _1 c0))))
(assert (= (min _1 c0) (min c0 _1)))

(assert (<= (min c0 c1) c0))
(assert (<= (min c0 c1) c1))
(assert (or (= c0 (min c0 c1)) (= c1 (min c0 c1))))
(assert (= (min c0 c1) (min c1 c0)))

