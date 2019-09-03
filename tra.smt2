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

; or-eq-sel function
(declare-fun or-eq-cell ((List Attr) (List value) Tuple) bool)

(assert (forall (t Tuple)
                (not (or-eq-cell [] [] t))))

(assert (forall ((a Attr) (as (List Attr))
                 (v Val) (vs (List Val))
                 (t Tuple))
                (= (or-eq-cell (insert a as) (insert v vs))
                   (or (= (get-cell a t) v)
                       (or-eq-cell as vs)))))

; sel-eqv-multi function
(declare-fun sel-eqv-multi ((List Attr) (List Val) Relation) Relation)

; sel-eqv-multi(a, v, []) = []
(assert (forall ((a Attr) (v Val))
                (! (= (sel-eqv-multi a v r_nil)
                      r_nil)
                   :pattern ((sel-eqv-multi a v r_nil)))))


(assert (forall ((as (List Attr))
                 (vs (List Val))
                 (t Tuple)
                 (r Relation))
                (! (= (sel-eqv-multi a v (insert t r))
                      (ite (or-eq-cell as vs t)
                           (insert t (sel-eqv a v r))
                           (sel-eqv a v r))))))

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

;; unit test section
(push)
(echo "Unit Test")

(declare-const v11 Val)
(declare-const v12 Val)
(declare-const v13 Val)
(declare-const v21 Val)
(declare-const v22 Val)
(declare-const v23 Val)

(define-fun c11 () Cell v11)
(define-fun c12 () Cell v12)
(define-fun c13 () Cell v13)
(define-fun c21 () Cell v21)
(define-fun c22 () Cell v22)
(define-fun c23 () Cell v23)

(declare-const t1 Tuple)
(declare-const t2 Tuple)
(declare-const t3 Tuple)
(declare-const t4 Tuple)
(declare-const a Relation)
(declare-const b Relation)
(declare-const c Relation)
(declare-const d Relation)

(push)
(echo "testing app...")
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= b (insert t3 (insert t4 r_nil))))
(assert (= c (insert t1 (insert t2 (insert t3 (insert t4 r_nil))))))
(assert (not
        (= (app a b) c)))
(check-sat)
(pop)

(push)
(echo "testing prod...")
(declare-const c14 Cell)
(declare-const t5 Tuple)
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= t3 (insert c14 t_nil)))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= b (insert t3 r_nil)))
(assert (= t4 (insert c11 (insert c12 (insert c13 (insert c14 t_nil))))))
(assert (= t5 (insert c21 (insert c22 (insert c23 (insert c14 t_nil))))))
(assert (= c (insert t4 (insert t5 r_nil))))
(assert (not
        (= (prod a b) c)))
(check-sat)
(pop)

(push)
(echo "testing proj...")
(declare-const l AttrList)
(declare-const t1n Tuple)
(declare-const t2n Tuple)
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= l (insert zero (insert two l_nil))))
(assert (= t1n (insert c11 (insert c13 t_nil))))
(assert (= t2n (insert c21 (insert c23 t_nil))))
(assert (= b (insert t1n (insert t2n r_nil))))
(assert (not
        (= (proj l a) b)))
(check-sat)
(pop)

(push)
(echo "testing sel-eq...")
(assert (not (= v12 v13)))
(assert (= v22 v23))
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= b (insert t2 r_nil)))
(assert (not
        (= (sel-eq one two a) b)))
(check-sat)
(pop)

(push)
(echo "testing sel-eqv...")
(assert (not (= v13 v23)))
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= b (insert t1 r_nil)))
(assert (not
        (= (sel-eqv two v13 a) b)))
(check-sat)
(pop)

(push)
(echo "testing equi-join...")
(define-fun c14 () Cell v13)
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= t3 (insert c14 t_nil)))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= b (insert t3 r_nil)))
(assert (not (= v23 v13)))
(assert (= t4 (insert c11 (insert c12 (insert c13 (insert c14 t_nil))))))
(assert (= c (insert t4 r_nil)))
(assert (not
        (= (equi-join two three a b) c)))
(check-sat)
(pop)

(push)
(echo "testing minus...")
(assert (= a (insert t1 (insert t2 (insert t3 r_nil)))))
(assert (= b (insert t2 r_nil)))
(assert (= c (insert t1 (insert t3 r_nil))))
(assert (not (= t1 t2)))
(assert (not (= t1 t3)))
(assert (not (= t2 t3)))
(assert (not
        (= (minus a b) c)))
(check-sat)
(pop)

(push)
(echo "testing upd...")
(declare-const v4 Val)
(define-fun c4 () Cell v4)
(assert (= t1 (insert c11 (insert c12 (insert c13 t_nil)))))
(assert (= t2 (insert c21 (insert c22 (insert c23 t_nil)))))
(assert (= a (insert t1 (insert t2 r_nil))))
(assert (= t3 (insert c11 (insert c4 (insert c13 t_nil)))))
(assert (= t4 (insert c21 (insert c4 (insert c23 t_nil)))))
(assert (= b (insert t3 (insert t4 r_nil))))
(assert (not
        (= (upd a one v4) b)))
(check-sat)
(pop)

(pop)
;; end of unit test section


;; Micro Benchmark 1
(push)
(echo "Micro Benchmark 1")

;; 0 - mid1, 1 - name1, 2 - addr1
(declare-const r1 Relation)
;; 0 - mid2, 1 - name2, 2 - afk2
(declare-const r2 Relation)
;; 0 - aid3, 1 - addr3
(declare-const r3 Relation)

;; 1 - name1, 2 - addr1
(define-fun l1 () AttrList (insert one (insert two l_nil)))
;; 1 - name2, 4 - addr3 (append attributes of r3 to that of r2)
(define-fun l2 () AttrList (insert one (insert four l_nil)))

;; Benchmark 1 - query part
(push)
(echo "Micro Benchmark 1 query")
(declare-const name Val)
(define-fun l3 () AttrList (insert two l_nil))
(define-fun l4 () AttrList (insert four l_nil))

(assert (not
        (=> (= (proj l1 r1) (proj l2 (equi-join two three r2 r3)))
            (= (proj l3 (sel-eqv one name r1)) (proj l4 (sel-eqv one name (equi-join two three r2 r3)))))))
(check-sat)
(pop)


;; Benchmark 1 - insertion part
(push)
(echo "Micro Benchmark 1 insertion")
(declare-const v1 Val)
(declare-const v2 Val)
(declare-const v3 Val)
(declare-const v4 Val)
(declare-const v5 Val)

(define-fun t1a () Tuple (insert v1 (insert v2 (insert v3 t_nil))))
(define-fun t2a () Tuple (insert v4 (insert v2 (insert v5 t_nil))))
(define-fun t3a () Tuple (insert v5 (insert v3 t_nil)))

(define-fun r1a () Relation (insert t1a r_nil))
(define-fun r2a () Relation (insert t2a r_nil))
(define-fun r3a () Relation (insert t3a r_nil))

;; TO BE GENERATED BY CLIENTS
(assert (= r_nil (equi-join two three r2 r3a)))
(assert (= r_nil (equi-join two three r2a r3)))

(push)
(assert (not
        (= (proj l1 r1a) (proj l2 (equi-join two three r2a r3a)))))
(check-sat)
(pop)

;; Better than before - previously it cannot prove the extra assertion
;; but now the solver can do it (the negation of (*) is unsat)

;; extra assertion (*)
(assert (= (proj l1 r1a) (proj l2 (equi-join two three r2a r3a))))

;; However, it is still unclear why the solver cannot prove (**) directly
;; it still needs to assume (*) in order to prove (**)

;; provable given extra assertion (**)
(assert (not
        (=> (= (proj l1 r1) (proj l2 (equi-join two three r2 r3)))
            (= (proj l1 (app r1 r1a)) (proj l2 (equi-join two three (app r2 r2a) (app r3 r3a)))))))

(check-sat)
(pop)

;; Benchmark 1 - deletion part
(push)
(echo "Micro Benchmark 1 - deletion")
(declare-const name Val)


(assert (not
        (=> (= (proj l1 r1) (proj l2 (equi-join two three r2 r3)))
            (= (proj l1 (minus r1 (sel-eqv one name r1)))
               (proj l2 (equi-join two three (minus r2 (sel-eqv one name r2)) (minus r3 (sel-in-eqv one name r2 r3))))))))
(check-sat)
(pop)

;; Benchmark 1 - update part
(push)
(echo "Micro Benchmark 1 - update")
(declare-const name Val)
(declare-const addr Val)


(assert (not
        (=> (= (proj l1 r1) (proj l2 (equi-join two three r2 r3)))
            (= (proj l1 (app (minus r1 (sel-eqv one name r1)) (upd (sel-eqv one name r1) two addr)))
               (proj l2 (equi-join two three r2 (app (minus r3 (sel-in-eqv one name r2 r3)) (upd (sel-in-eqv one name r2 r3) four addr))))))))
(check-sat)
(pop)

(pop)
;; end of Micro Benchmark 1

;; Micro Benchmark 2
(push)
(echo "Micro Benchmark 2")

; 0 - mid', 1 - name', 2 - addr', 3 - email'
(declare-const r1 Relation)
; 0 - mid, 1 - name, 2 - afk, 3 - efk
(declare-const r2 Relation)
; 0 - aid, 1 - addr
(declare-const r3 Relation)
; 0 - eid, 1 - email
(declare-const r4 Relation)

(define-fun l1 () AttrList (insert one (insert two l_nil)))
(define-fun l2 () AttrList (insert one (insert five l_nil)))
(define-fun l3 () AttrList (insert one (insert three l_nil)))
(define-fun l4 () AttrList (insert one (insert five l_nil)))

;; Micro Benchmark 2 - query part
(push)
(echo "Micro Benchmark 2 - query")
(declare-const name Val)
(define-fun l5 () AttrList (insert two l_nil))
(define-fun l6 () AttrList (insert five l_nil))

(assert (not
        (=> (and (= (proj l1 r1) (proj l2 (equi-join two four r2 r3)))
                 (= (proj l3 r1) (proj l4 (equi-join three four r2 r4))))
            (= (proj l5 (sel-eqv one name r1)) (proj l6 (sel-eqv one name (equi-join two four r2 r3)))))))
(check-sat)
(pop)

;; Micro Benchmark 2 - insertion part
(push)
(echo "Micro Benchmark 2 - insertion")
(declare-const v0 Val)
(declare-const v1 Val)
(declare-const v2 Val)
(declare-const v3 Val)
(declare-const v4 Val)
(declare-const v5 Val)
(declare-const v6 Val)

(define-fun t1a () Tuple (insert v6 (insert v1 (insert v4 (insert v5 t_nil)))))
(define-fun t2a () Tuple (insert v0 (insert v1 (insert v2 (insert v3 t_nil)))))
(define-fun t3a () Tuple (insert v2 (insert v4 t_nil)))
(define-fun t4a () Tuple (insert v3 (insert v5 t_nil)))

(define-fun r1a () Relation (insert t1a r_nil))
(define-fun r2a () Relation (insert t2a r_nil))
(define-fun r3a () Relation (insert t3a r_nil))
(define-fun r4a () Relation (insert t4a r_nil))

;; TO BE GENERATED BY CLIENTS
(assert (= r_nil (equi-join two four r2 r3a)))
(assert (= r_nil (equi-join two four r2a r3)))
(assert (= r_nil (equi-join three four r2 r4a)))
(assert (= r_nil (equi-join three four r2a r4)))

(push)
(assert (not
        (and (= (proj l1 r1a) (proj l2 (equi-join two four r2a r3a)))
             (= (proj l3 r1a) (proj l4 (equi-join three four r2a r4a))))))
(check-sat)
(pop)

;; extra assertion
;; proven above
(assert (and (= (proj l1 r1a) (proj l2 (equi-join two four r2a r3a)))
             (= (proj l3 r1a) (proj l4 (equi-join three four r2a r4a)))))

;; provable given extra assertion
(assert (not
        (=> (and (= (proj l1 r1) (proj l2 (equi-join two four r2 r3)))
                 (= (proj l3 r1) (proj l4 (equi-join three four r2 r4))))
            (and (= (proj l1 (app r1 r1a)) (proj l2 (equi-join two four (app r2 r2a) (app r3 r3a))))
                 (= (proj l3 (app r1 r1a)) (proj l4 (equi-join three four (app r2 r2a) (app r4 r4a))))))))
(check-sat)
(pop)

;; Micro Benchmark 2 - deletion part
(push)
(echo "Micro Benchmark 2 - deletion")
(declare-const name Val)

;; needs a way to transform the invariant
(assert (not
        (=> (and (= (proj l1 r1) (proj l2 (equi-join two four r2 r3)))
                 (= (proj l3 r1) (proj l4 (equi-join three four r2 r4))))
            (and (= (proj l1 (minus r1 (sel-eqv one name r1))) (proj l2 (equi-join two four r2 (minus r3 (sel-in-eqv one name r2 r3)))))
                 (= (proj l3 (minus r1 (sel-eqv one name r1))) (proj l4 (equi-join three four r2 (minus r4 (sel-in-eqv one name r2 r4)))))))))
(check-sat)
(pop)

;; Micro Benchmark 2 - update part
(push)
(echo "Micro Benchmark 2 - update")
(declare-const name Val)
(declare-const addr Val)
(declare-const email Val)


(assert (not
        (=> (and (= (proj l1 r1) (proj l2 (equi-join two four r2 r3)))
                 (= (proj l3 r1) (proj l4 (equi-join three four r2 r4))))
            (and (= (proj l1 (app (minus r1 (sel-eqv one name r1)) (upd (sel-eqv one name r1) two addr)))
                    (proj l2 (equi-join two four r2 (app (minus r3 (sel-in-eqv one name r2 r3)) (upd (sel-in-eqv one name r2 r3) five addr)))))
                 (= (proj l3 (app (minus r1 (sel-eqv one name r1)) (upd (sel-eqv one name r1) three email)))
                    (proj l4 (equi-join three four r2 (app (minus r4 (sel-in-eqv one name r2 r4)) (upd (sel-in-eqv one name r2 r4) five email)))))))))
(check-sat)
(pop)

(push)
(echo "Micro Benchmark 2 - single update")
(declare-const name Val)
(declare-const addr Val)
(declare-const email Val)


(assert (not
        (=> (and (= (proj l1 r1) (proj l2 (equi-join two four r2 r3)))
                 (= (proj l3 r1) (proj l4 (equi-join three four r2 r4))))
            (and (= (proj l1 (app (minus r1 (sel-eqv one name r1)) (upd (sel-eqv one name r1) two addr)))
                    (proj l2 (equi-join two four r2 (app (minus r3 (sel-in-eqv one name r2 r3)) (upd (sel-in-eqv one name r2 r3) five addr)))))
                 (= (proj l3 (app (minus r1 (sel-eqv one name r1)) (upd (sel-eqv one name r1) two addr)))
                    (proj l4 (equi-join three four r2 r4)))))))
(check-sat)
(pop)

(pop)
;; end of Micro Benchmark 2

(push)
(echo "Micro Benchmark 3")

; 0 - mid, 1 - name, 2 - afk
(declare-const r1 Relation)
; 0 - aid, 1 - addr, 2 - zip
(declare-const r2 Relation)
; 0 - mid', 1 - name', 2 - addr', 3 - zip'
(declare-const r3 Relation)

(define-fun l1 () AttrList (insert one (insert four (insert five l_nil))))
(define-fun l2 () AttrList (insert one (insert two (insert three l_nil))))

(define-fun inv () Bool (= (proj l1 (equi-join two three r1 r2)) (proj l2 r3)))

(push)
(echo "Micro Benchmark 3 - update")
(declare-const name Val)
(declare-const addr Val)
(declare-const zip Val)

(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)
(declare-const rr7 Relation)

(assert (= rr6 (app (minus r2 (sel-in-eqv one name r1 r2)) (upd (sel-in-eqv one name r1 r2) four addr))))
(assert (= rr7 (app (minus r3 (sel-eqv one name r3)) (upd (sel-eqv one name r3) two addr))))

(assert (= rr4 (app (minus rr6 (sel-in-eqv one name r1 rr6)) (upd (sel-in-eqv one name r1 rr6) five zip))))
(assert (= rr5 (app (minus rr7 (sel-eqv one name rr7)) (upd (sel-eqv one name rr7) three zip))))

(assert (not
        (=> inv
            (= (proj l1 (equi-join two three r1 rr4))
               (proj l2 rr5)))))

(check-sat)
(pop)

(push)
(echo "Micro Benchmark 3 - update commutative 1")
(declare-const name Val)
(declare-const addr Val)
(declare-const zip Val)

(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)
(declare-const rr7 Relation)

(assert (= rr6 (app (minus r2 (sel-in-eqv one name r1 r2)) (upd (sel-in-eqv one name r1 r2) five zip))))
(assert (= rr7 (app (minus r3 (sel-eqv one name r3)) (upd (sel-eqv one name r3) two addr))))

(assert (= rr4 (app (minus rr6 (sel-in-eqv one name r1 rr6)) (upd (sel-in-eqv one name r1 rr6) four addr))))
(assert (= rr5 (app (minus rr7 (sel-eqv one name rr7)) (upd (sel-eqv one name rr7) three zip))))

(assert (not
        (=> inv
            (= (proj l1 (equi-join two three r1 rr4))
               (proj l2 rr5)))))

(check-sat)
(pop)

(push)
(echo "Micro Benchmark 3 - update commutative 2")
(declare-const name Val)
(declare-const addr Val)
(declare-const zip Val)

(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)
(declare-const rr7 Relation)

(assert (= rr6 (app (minus r2 (sel-in-eqv one name r1 r2)) (upd (sel-in-eqv one name r1 r2) four addr))))
(assert (= rr7 (app (minus r3 (sel-eqv one name r3)) (upd (sel-eqv one name r3) three zip))))

(assert (= rr4 (app (minus rr6 (sel-in-eqv one name r1 rr6)) (upd (sel-in-eqv one name r1 rr6) five zip))))
(assert (= rr5 (app (minus rr7 (sel-eqv one name rr7)) (upd (sel-eqv one name rr7) two addr))))

(assert (not
        (=> inv
            (= (proj l1 (equi-join two three r1 rr4))
               (proj l2 rr5)))))

(check-sat)
(pop)

(pop)
; end of Micro Benchmark 3

(push)
(echo "Micro Benchmark 4")

; 0 - mid, 1 - name, 2 - afk
(declare-const r1 Relation)
; 0 - aid, 1 - addr, 2 - city, 3 - state, 4 - zip
(declare-const r2 Relation)
; 0 - mid', 1 - name', 2 - addr', 3 - city', 4 - state', 5 - zip'
(declare-const r3 Relation)

(define-fun l1 () AttrList (insert one (insert four (insert five (insert six (insert seven l_nil))))))
(define-fun l2 () AttrList (insert one (insert two (insert three (insert four (insert five l_nil))))))

(define-fun inv () Bool (= (proj l1 (equi-join two three r1 r2)) (proj l2 r3)))

(push)
(echo "Micro Benchmark 4 - update")
(declare-const name Val)
(declare-const addr Val)
(declare-const city Val)
(declare-const state Val)
(declare-const zip Val)

(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)
(declare-const rr7 Relation)
(declare-const rr8 Relation)
(declare-const rr9 Relation)
(declare-const rr0 Relation)
(declare-const rr1 Relation)

(assert (= rr0 (app (minus r2 (sel-in-eqv one name r1 r2)) (upd (sel-in-eqv one name r1 r2) four addr))))
(assert (= rr1 (app (minus r3 (sel-eqv one name r3)) (upd (sel-eqv one name r3) two addr))))

(assert (= rr8 (app (minus rr0 (sel-in-eqv one name r1 rr0)) (upd (sel-in-eqv one name r1 rr0) five city))))
(assert (= rr9 (app (minus rr1 (sel-eqv one name rr1)) (upd (sel-eqv one name rr1) three city))))

(assert (= rr6 (app (minus rr8 (sel-in-eqv one name r1 rr8)) (upd (sel-in-eqv one name r1 rr8) six state))))
(assert (= rr7 (app (minus rr9 (sel-eqv one name rr9)) (upd (sel-eqv one name rr9) four state))))

(assert (= rr4 (app (minus rr6 (sel-in-eqv one name r1 rr6)) (upd (sel-in-eqv one name r1 rr6) seven zip))))
(assert (= rr5 (app (minus rr7 (sel-eqv one name rr7)) (upd (sel-eqv one name rr7) five zip))))

(assert (not
        (=> inv
            (= (proj l1 (equi-join two three r1 rr4))
               (proj l2 rr5)))))

;(check-sat)
(echo "Provable in ~ 160s, checking disabled by default")
(pop)

(pop)
; end of Micro Benchmark 4

; Micro Benchmark 5
(push)
(echo "Micro Benchmark 5")

; 0 - sid', 1 - sname', 2 - filter'
(declare-const r1 Relation)
; 0 - sid, 1 - sname, 2 - fid_fk
(declare-const r2 Relation)
; 0 - fid, 1 - fname, 2 - params
(declare-const r3 Relation)

(define-fun l1 () AttrList (insert zero (insert one (insert two l_nil))))
(define-fun l2 () AttrList (insert zero (insert one (insert five l_nil))))

(define-fun inv () Bool (= (proj l1 r1) (proj l2 (equi-join two three r2 r3))))

(push)
(echo "Micro Benchmark 5 - update")
(declare-const id Val)
(declare-const name Val)
(declare-const fltr Val)

(declare-const rr1 Relation)
(declare-const rr2 Relation)
(declare-const rr3 Relation)
(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)

(assert (= rr1 (app (minus rr4 (sel-eqv zero id rr4)) (upd (sel-eqv zero id rr4) one name))))
(assert (= rr2 (app (minus r2 (sel-eqv zero id r2)) (upd (sel-eqv zero id r2) one name))))

(assert (= rr3 (app (minus r3 (sel-in-eqv zero id r2 r3)) (upd (sel-in-eqv zero id r2 r3) five fltr))))
(assert (= rr4 (app (minus r1 (sel-eqv zero id r1)) (upd (sel-eqv zero id r1) two fltr))))

(assert (not
        (=> inv
            (= (proj l1 rr1)
               (proj l2 (equi-join two three rr2 rr3))))))
(check-sat)
(pop)

(push)
(echo "Micro Benchmark 5 - update")
(declare-const id Val)
(declare-const name Val)
(declare-const fltr Val)

(declare-const rr1 Relation)
(declare-const rr2 Relation)
(declare-const rr3 Relation)
(declare-const rr4 Relation)
(declare-const rr5 Relation)
(declare-const rr6 Relation)

(assert (= rr1 (app (minus rr4 (sel-eqv zero id rr4)) (upd (sel-eqv zero id rr4) two fltr))))
(assert (= rr2 (app (minus r2 (sel-eqv zero id r2)) (upd (sel-eqv zero id r2) one name))))

(assert (= rr3 (app (minus r3 (sel-in-eqv zero id r2 r3)) (upd (sel-in-eqv zero id r2 r3) five fltr))))
(assert (= rr4 (app (minus r1 (sel-eqv zero id r1)) (upd (sel-eqv zero id r1) one name))))

(assert (not
        (=> inv
            (= (proj l1 rr1)
               (proj l2 (equi-join two three rr2 rr3))))))
(check-sat)
(pop)

(pop)
; end of Micro Benchmark 5

