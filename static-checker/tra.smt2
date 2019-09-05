(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :timeout 300000)

(declare-sort Val)
(declare-sort T)
(define-sort Attr () (List T))
(define-sort AttrList () (List Attr))
(define-sort Cell () Val)
(define-sort Tuple () (List Cell))
(define-sort Relation () (List Tuple))

;; aliases
(define-fun a_nil () Attr (as nil Attr))
(define-fun l_nil () AttrList (as nil AttrList))
(define-fun t_nil () Tuple (as nil Tuple))
(define-fun r_nil () Relation (as nil Relation))


;; number constants
(declare-const n1 T)
(define-fun zero () Attr a_nil)
(define-fun one () Attr (insert n1 zero))
(define-fun two () Attr (insert n1 one))
(define-fun three () Attr (insert n1 two))
(define-fun four () Attr (insert n1 three))
(define-fun five () Attr (insert n1 four))
(define-fun six () Attr (insert n1 five))
(define-fun seven () Attr (insert n1 six))


;; axiom section

;; app function
;; Input: Relation r1, Relation r2
;; Output: r1 ++ r2
(declare-fun app (Relation Relation) Relation)

; app([], r2) = r2
(assert (forall ((r2 Relation))
                (! (= (app r_nil r2)
                      r2)
                   :pattern ((app r_nil r2)))))

; app(t :: r, r2) = t :: app(r, r2)
(assert (forall ((t Tuple) (r Relation) (r2 Relation))
                (! (= (app (insert t r) r2)
                      (insert t (app r r2)))
                   :pattern ((app (insert t r) r2)))))

;; cat-tuple function
;; Input: Tuple t1, Tuple t2
;; Output: t1 ++ t2
(declare-fun cat-tuple (Tuple Tuple) Tuple)

; cat-tuple([], t2) = t2
(assert (forall ((t2 Tuple))
                (! (= (cat-tuple t_nil t2)
                      t2)
                   :pattern ((cat-tuple t_nil t2)))))

; cat-tuple(c :: t, t2) = c :: cat-tuple(t, t2)
(assert (forall ((c Cell) (t Tuple) (t2 Tuple))
                (! (= (cat-tuple (insert c t) t2)
                      (insert c (cat-tuple t t2)))
                   :pattern ((cat-tuple (insert c t) t2)))))

;; prod function
;; Input: Relation r1, Relation r2
;; Output: r1 x r2
(declare-fun prod (Relation Relation) Relation)
(declare-fun prod-aux (Tuple Relation) Relation)

; prod-aux(t, []) = []
(assert (forall ((t Tuple))
                (! (= (prod-aux t r_nil)
                      r_nil)
                   :pattern ((prod-aux t r_nil)))))

; prod-aux(t, h :: r) = cat-tuple(t, h) :: prod-aux(t, r)
(assert (forall ((t Tuple) (h Tuple) (r Relation))
                (! (= (prod-aux t (insert h r))
                      (insert (cat-tuple t h) (prod-aux t r)))
                   :pattern ((prod-aux t (insert h r))))))

; prod([], r2) = []
(assert (forall ((r2 Relation))
                (! (= (prod r_nil r2)
                      r_nil)
                   :pattern ((prod r_nil r2)))))

; prod(t :: r, r2) = prod-aux(t, r2) ++ prod(r, r2)
(assert (forall ((t Tuple) (r Relation) (r2 Relation))
                (! (= (prod (insert t r) r2)
                      (app (prod-aux t r2) (prod r r2)))
                   :pattern ((prod (insert t r) r2)))))

;; proj function
;; Input: AttrList l, Relation r
;; Output: Relation \Pi_l(r)
(declare-fun proj (AttrList Relation) Relation)
(declare-fun proj-tuple (AttrList Tuple) Tuple)
(declare-fun get-cell (Attr Tuple) Cell)


; get-cell(a, c :: t) = (a == nil) ? c : get-cell(tail(a), t)
(assert (forall ((a Attr) (c Cell) (t Tuple))
                (! (= (get-cell a (insert c t))
                      (ite (= a a_nil)
                           c
                           (get-cell (tail a) t)))
                   :pattern (get-cell a (insert c t)))))

; proj-tuple([], t) = []
(assert (forall ((t Tuple))
                (! (= (proj-tuple l_nil t)
                      t_nil)
                   :pattern (proj-tuple l_nil t))))

; proj-tuple(a :: l, t) = get-cell(a, t) :: proj-tuple(l, t)
(assert (forall ((a Attr) (l AttrList) (t Tuple))
                (! (= (proj-tuple (insert a l) t)
                      (insert (get-cell a t) (proj-tuple l t)))
                   :pattern (proj-tuple (insert a l) t))))

; proj(l, []) = []
(assert (forall ((l AttrList))
                (! (= (proj l r_nil)
                      r_nil)
                   :pattern (proj l r_nil))))

; proj(l, t :: r) = proj-tuple(l, t) :: proj(l, r)
(assert (forall ((l AttrList) (t Tuple) (r Relation))
                (! (= (proj l (insert t r))
                      (insert (proj-tuple l t) (proj l r)))
                   :pattern ((proj l (insert t r))))))

;; sel-eq function
;; Input: Attr a1, Attr a2, Relation r
;; Output: Relation \sigma_{a1 = a2}(r)
(declare-fun sel-eq (Attr Attr Relation) Relation)

; sel-eq(a1, a2, []) = []
(assert (forall ((a1 Attr) (a2 Attr))
                (! (= (sel-eq a1 a2 r_nil)
                      r_nil)
                   :pattern ((sel-eq a1 a2 r_nil)))))

; sel-eq(a1, a2, t :: r) = (t.a1 == t.a2) ? t :: sel-eq(a1, a2, r) : sel-eq(a1, a2, r)
(assert (forall ((a1 Attr) (a2 Attr) (t Tuple) (r Relation))
                (! (= (sel-eq a1 a2 (insert t r))
                      (ite (= (get-cell a1 t) (get-cell a2 t))
                           (insert t (sel-eq a1 a2 r))
                           (sel-eq a1 a2 r)))
                   :pattern ((sel-eq a1 a2 (insert t r))))))

;; sel-eqv function
;; Input: Attr a, Val v, Relation r
;; Output: Relation \sigma_{a = v}(r)
(declare-fun sel-eqv (Attr Val Relation) Relation)

; sel-eqv(a, v, []) = []
(assert (forall ((a Attr) (v Val))
                (! (= (sel-eqv a v r_nil)
                      r_nil)
                   :pattern ((sel-eqv a v r_nil)))))

; sel-eqv(a, v, t :: r) = (t.a == v) ? t :: sel-eq(a1, a2, r) : sel-eq(a1, a2, r)
(assert (forall ((a Attr) (v Val) (t Tuple) (r Relation))
                (! (= (sel-eqv a v (insert t r))
                      (ite (= (get-cell a t) v)
                           (insert t (sel-eqv a v r))
                           (sel-eqv a v r)))
                   :pattern ((sel-eqv a v (insert t r))))))

; ; or-eq-sel function
; (declare-fun or-eq-cell ((List Attr) (List value) Tuple) bool)
; 
; (assert (forall (t Tuple)
;                 (not (or-eq-cell [] [] t))))
; 
; (assert (forall ((a Attr) (as (List Attr))
;                  (v Val) (vs (List Val))
;                  (t Tuple))
;                 (= (or-eq-cell (insert a as) (insert v vs))
;                    (or (= (get-cell a t) v)
;                        (or-eq-cell as vs)))))
; 
; ; sel-eqv-multi function
; (declare-fun sel-eqv-multi ((List Attr) (List Val) Relation) Relation)
; 
; ; sel-eqv-multi(a, v, []) = []
; (assert (forall ((a Attr) (v Val))
;                 (! (= (sel-eqv-multi a v r_nil)
;                       r_nil)
;                    :pattern ((sel-eqv-multi a v r_nil)))))
; 
; 
; (assert (forall ((as (List Attr))
;                  (vs (List Val))
;                  (t Tuple)
;                  (r Relation))
;                 (! (= (sel-eqv-multi a v (insert t r))
;                       (ite (or-eq-cell as vs t)
;                            (insert t (sel-eqv a v r))
;                            (sel-eqv a v r))))))

;; equi-join function
;; Input: Attr a1, Attr a2, Relation r1, Relation r2
;; OUtput: Relation r1 \bowtie_{r1.a1 = r2.a2} r2
(declare-fun equi-join (Attr Attr Relation Relation) Relation)

; syntactic sugar of sel-eq and prod
(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation))
                (! (= (equi-join a1 a2 r1 r2)
                      (sel-eq a1 a2 (prod r1 r2)))
                   :pattern ((equi-join a1 a2 r1 r2)))))

;; minus function
;; Input: Relation r1, Relation r2
;; Output: r1 - r2
(declare-fun minus (Relation Relation) Relation)
(declare-fun minus-one (Relation Tuple) Relation)

; minus-one([], t) = []
(assert (forall ((t Tuple))
                (! (= (minus-one r_nil t)
                      r_nil)
                   :pattern ((minus-one r_nil t)))))

; minus-one(t1 :: r1, t2) = (t1 == t2) ? r1 : t1 :: minus-one(r1, t2)
(assert (forall ((t1 Tuple) (r1 Relation) (t2 Tuple))
                (! (= (minus-one (insert t1 r1) t2)
                      (ite (= t1 t2)
                           r1
                           (insert t1 (minus-one r1 t2))))
                   :pattern ((minus-one (insert t1 r1) t2)))))

; minus(r1, []) = r1
(assert (forall ((r1 Relation))
                (! (= (minus r1 r_nil)
                      r1)
                   :pattern ((minus r1 r_nil)))))

; minus(r1, t :: r2) = minus(minus-one(r1, t), r2)
(assert (forall ((r1 Relation) (t Tuple) (r2 Relation))
                (! (= (minus r1 (insert t r2))
                      (minus (minus-one r1 t) r2))
                   :pattern (minus r1 (insert t r2)))))

;; upd function
;; Input: Relation r, Attr a, Val v
;; Output: Relation r<a, v>
(declare-fun upd (Relation Attr Val) Relation)
(declare-fun upd-tuple (Tuple Attr Val) Tuple)

; upd-tuple([], a, v) = []
(assert (forall ((a Attr) (v Val))
                (! (= (upd-tuple t_nil a v)
                      t_nil)
                   :pattern (upd-tuple t_nil a v))))

; upd-tuple(c :: t, a, v) = (a == nil) ? (v :: t) : (c :: upd-tuple(t, tail(a), v))
(assert (forall ((c Cell) (t Tuple) (a Attr) (v Val))
                (! (= (upd-tuple (insert c t) a v)
                      (ite (= a a_nil)
                           (insert v t)
                           (insert c (upd-tuple t (tail a) v))))
                   :pattern ((upd-tuple (insert c t) a v)))))

; upd([], a, v) = []
(assert (forall ((a Attr) (v Val))
                (! (= (upd r_nil a v)
                       r_nil)
                   :pattern ((upd r_nil a v)))))

; upd(t :: r, a, v) = upd-tuple(t, a, v) :: upd(r, a, v)
(assert (forall ((t Tuple) (r Relation) (a Attr) (v Val))
                (! (= (upd (insert t r) a v)
                      (insert (upd-tuple t a v) (upd r a v)))
                   :pattern ((upd (insert t r) a v)))))


;; theorem section

; app(r, []) = r
(assert (forall ((r Relation))
                (! (= (app r r_nil)
                      r)
                   :pattern (app r r_nil))))

; equi-join(r, []) = []
(assert (forall ((a1 Attr) (a2 Attr) (r Relation))
                (! (= (equi-join a1 a2 r r_nil)
                   r_nil)
                   :pattern (equi-join a1 a2 r r_nil))))

; equi-join app distributive
(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation) (r3 Relation))
                (! (= (equi-join a1 a2 r1 (app r2 r3))
                      (app (equi-join a1 a2 r1 r2) (equi-join a1 a2 r1 r3)))
                   :pattern ((equi-join a1 a2 r1 (app r2 r3))))))

(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation) (r3 Relation))
                (! (= (equi-join a1 a2 (app r1 r2) r3)
                      (app (equi-join a1 a2 r1 r3) (equi-join a1 a2 r2 r3)))
                   :pattern ((equi-join a1 a2 (app r1 r2) r3)))))

; proj app distributive
(assert (forall ((l AttrList) (r1 Relation) (r2 Relation))
                (! (= (proj l (app r1 r2))
                      (app (proj l r1) (proj l r2)))
                   :pattern ((proj l (app r1 r2))))))


;; sel-in simplification
; sel-in-eqv
(declare-fun sel-in-eqv (Attr Val Relation Relation) Relation)

(assert (forall ((a1 Attr) (a2 Attr) (a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= (equi-join a1 a2 r1 (sel-in-eqv a v r1 r2))
                      (sel-eqv a v (equi-join a1 a2 r1 r2)))
                   :pattern ((equi-join a1 a2 r1 (sel-in-eqv a v r1 r2))))))

(assert (forall ((a1 Attr) (a2 Attr) (a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= (equi-join a1 a2 (sel-in-eqv a v r1 r2) r1)
                      (sel-eqv a v (equi-join a1 a2 r1 r2)))
                   :pattern ((equi-join a1 a2 (sel-in-eqv a v r1 r2) r1)))))

;; sel-eqv idempotence
(assert (forall ((a Attr) (v Val) (r Relation))
                (! (= (sel-eqv a v (sel-eqv a v r))
                      (sel-eqv a v r))
                   :pattern ((sel-eqv a v (sel-eqv a v r))))))

;; minus same
(assert (forall ((r Relation))
                (! (= (minus r r)
                   r_nil)
                   :pattern ((minus r r)))))

;; sub-set
(declare-fun sub-set (Relation Relation) Bool)

(assert (forall ((a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= true (sub-set (sel-in-eqv a v r1 r2) r2))
                   :pattern ((sel-in-eqv a v r1 r2)))))

(assert (forall ((a Attr) (v Val) (r Relation))
                (! (= true (sub-set (sel-eqv a v r) r))
                   :pattern ((sel-eqv a v r)))))

(assert (forall ((l AttrList) (r1 Relation) (r2 Relation))
                (=> (= true (sub-set r2 r1))
                    (= true (sub-set (proj l r2) (proj l r1))))))

; subset(r2, r1) => r1 - r2 + r2 = r1
(assert (forall ((r1 Relation) (r2 Relation))
                (! (=> (= true (sub-set r2 r1))
                       (= (app (minus r1 r2) r2)
                          r1))
                   :pattern ((app (minus r1 r2) r2)))))


; equi-join minus distributive
(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation) (r3 Relation))
                (! (=> (= true (sub-set r2 r1))
                       (= (equi-join a1 a2 (minus r1 r2) r3)
                          (minus (equi-join a1 a2 r1 r3) (equi-join a1 a2 r2 r3))))
                   :pattern ((equi-join a1 a2 (minus r1 r2) r3)))))

(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation) (r3 Relation))
                (! (=> (= true (sub-set r3 r2))
                       (= (equi-join a1 a2 r1 (minus r2 r3))
                          (minus (equi-join a1 a2 r1 r2) (equi-join a1 a2 r1 r3))))
                   :pattern ((equi-join a1 a2 r1 (minus r2 r3))))))

; proj minus distributive
(assert (forall ((l AttrList) (r1 Relation) (r2 Relation))
                (! (=> (= true (sub-set r2 r1))
                       (= (proj l (minus r1 r2))
                          (minus (proj l r1) (proj l r2))))
                   :pattern ((proj l (minus r1 r2))))))

; sel-eqv equi-join associative
(assert (forall ((a1 Attr) (a2 Attr) (a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= (equi-join a1 a2 (sel-eqv a v r1) r2)
                      (sel-eqv a v (equi-join a1 a2 r1 r2)))
                   :pattern (equi-join a1 a2 (sel-eqv a v r1) r2))))

; proj subsequence (restricted)
; (should define a same-subseq predicate, to be exact)
; list tail
(assert (forall ((l1 AttrList) (l2 AttrList) (r1 Relation) (r2 Relation))
                (=> (= (proj l1 r1) (proj l2 r2))
                    (= (proj (tail l1) r1) (proj (tail l2) r2)))))

; list head
(assert (forall ((l1 AttrList) (l2 AttrList) (r1 Relation) (r2 Relation))
                (=> (= (proj l1 r1) (proj l2 r2))
                    (= (proj (insert (head l1) l_nil) r1) (proj (insert (head l2) l_nil) r2)))))

; proj sel-eqv introduction
; uninterpreted, generated by list-pair
(declare-fun same-index (Attr Attr AttrList AttrList) Bool)

(assert (forall ((l1 AttrList) (l2 AttrList) (r1 Relation) (r2 Relation) (a1 Attr) (a2 Attr) (v Val))
                (=> (and (= (proj l1 r1) (proj l2 r2)) (same-index a1 a2 l1 l2))
                    (= (proj l1 (sel-eqv a1 v r1)) (proj l2 (sel-eqv a2 v r2))))))

; proj upd introduction
(assert (forall ((l1 AttrList) (l2 AttrList) (r1 Relation) (r2 Relation) (a1 Attr) (a2 Attr) (v Val))
                (=> (and (= (proj l1 r1) (proj l2 r2)) (same-index a1 a2 l1 l2))
                    (= (proj l1 (upd r1 a1 v)) (proj l2 (upd r2 a2 v))))))

; same-index emission
(declare-fun list-pair (AttrList AttrList AttrList AttrList) Bool)

(assert (forall ((l1 AttrList) (r1 Relation) (l2 AttrList) (r2 Relation))
                (=> (= (proj l1 r1) (proj l2 r2))
                    (list-pair l1 l2 l1 l2))))

(assert (forall ((l1 AttrList) (l2 AttrList) (l3 AttrList) (l4 AttrList))
                (! (=> (list-pair l1 l2 l3 l4)
                       (and (same-index (head l1) (head l2) l3 l4)
                            (list-pair (tail l1) (tail l2) l3 l4)))
                   :pattern (list-pair l1 l2 l3 l4))))

;; check if an attribute is a member of a list
(declare-fun mem-list (Attr AttrList) Bool)

(assert (forall ((a Attr))
                (! (= (mem-list a l_nil)
                   false)
                   :pattern ((mem-list a l_nil)))))

(assert (forall ((a Attr) (h Attr) (t AttrList))
                (! (= (mem-list a (insert h t))
                      (ite (= a h)
                           true
                           (mem-list a t)))
                   :pattern ((mem-list a (insert h t))))))

; mem-list(a, l) = false => proj(l, upd(r, a, v)) = proj(l, r)
(assert (forall ((l AttrList) (r Relation) (a Attr) (v Val))
                (! (=> (= false (mem-list a l))
                       (= (proj l (upd r a v))
                          (proj l r)))
                   :pattern ((proj l (upd r a v))))))


; r1 + r2 - r2 = r1
(assert (forall ((r1 Relation) (r2 Relation))
                (! (= (minus (app r1 r2) r2)
                      r1)
                   :pattern ((minus (app r1 r2) r2)))))

; speedup?
; sel app dist
(assert (forall ((a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= (sel-eqv a v (app r1 r2))
                      (app (sel-eqv a v r1) (sel-eqv a v r2)))
                   :pattern ((sel-eqv a v (app r1 r2))))))

; speedup?
; sel minus dist
(assert (forall ((a Attr) (v Val) (r1 Relation) (r2 Relation))
                (! (= (sel-eqv a v (minus r1 r2))
                      (minus (sel-eqv a v r1) (sel-eqv a v r2)))
                   :pattern ((sel-eqv a v (minus r1 r2))))))

; sel upd sel simpl
(assert (forall ((a1 Attr) (v1 Val) (r Relation) (a2 Attr) (v2 Val))
                (! (=> (not (= a1 a2))
                       (= (sel-eqv a1 v1 (upd (sel-eqv a1 v1 r) a2 v2))
                          (upd (sel-eqv a1 v1 r) a2 v2)))
                   :pattern ((sel-eqv a1 v1 (upd (sel-eqv a1 v1 r) a2 v2))))))

; upd commutative
(assert (forall ((r Relation) (a1 Attr) (v1 Val) (a2 Attr) (v2 Val))
                (! (=> (not (= a1 a2))
                       (= (upd (upd r a1 v1) a2 v2)
                          (upd (upd r a2 v2) a1 v1)))
                   :pattern ((upd (upd r a1 v1) a2 v2)))))

; upd join comm
(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (a Attr) (v Val) (r2 Relation))
                (! (=> (and (not (= a1 a)) (not (= a2 a)))
                       (= (equi-join a1 a2 (upd r1 a v) r2)
                       (upd (equi-join a1 a2 r1 r2) a v)))
                   :pattern ((equi-join a1 a2 (upd r1 a v) r2)))))

; interesting
(assert (forall ((a1 Attr) (a2 Attr) (r1 Relation) (r2 Relation) (a Attr) (v Val))
                (! (=> (and (not (= a1 a)) (not (= a2 a)))
                       (= (equi-join a1 a2 r1 (upd r2 a v))
                       (upd (equi-join a1 a2 r1 r2) a v)))
                   :pattern ((equi-join a1 a2 r1 (upd r2 a v))))))

;; end of theorem section
