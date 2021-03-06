#lang racket
(require redex)
(require rackunit)

(define k 0)

(define-language k-cfa
  [Σ (e ρ σ a t)]
  [ρ ((v a) ...)]
  [σ ((a (D ...)) ...)]
  [e ::=
     val
     ref
     (label : (e e))
     (label : (prim e))]
  [val ::=
       atom
       lam]
  [atom ::=
        const
        N]
  [lam (label : (λ (v) e))]
  [const (label : number)]
  [prim ::=
        (label : add1)]
  [clo ::=
       (lam ρ)]
  [D ::=
     clo
     atom
     κ]
  [κ ::=
     (mt)
     (add1k a)
     (ar e ρ a)
     (fn lam ρ a)]
  [ref (label : v)]
  [v variable-not-otherwise-mentioned]
  [label natural]
  [contour ::=
           ε
           (label contour)]
  [labelOrVar ::=
              label
              v]
  [a b c ::= (labelOrVar × contour)]
  [t u ::= contour])

(define (labelFrom1 e)
  (define-values (res count) (add-labels e 1 add1))
  res)

(define (add-labels e lab inc)
  (match e
    [`(,e0 ,e1)
     (define-values (le0 c0) (add-labels e0 (inc lab) inc))
     (define-values (le1 c1) (add-labels e1 c0 inc))
     (values `(,lab : (,le0 ,le1))
             c1)]
    [`(λ (,x) ,e0)
     (define-values (le0 count) (add-labels e0 (inc lab) inc))
     (values `(,lab : (λ (,x)
                        ,le0))
             count)]
    [(? number? n)
     (values `(,lab : ,n)
             (inc lab))]
    [(? symbol? s)
     (values `(,lab : ,s)
             (inc lab))]))

;; Annotates a bar expression with labels and injects it into a starting Σ
(define (inject e)
  `(,(labelFrom1 e)
    ()
    (((0 × ε) ((mt))))
    (0 × ε)
    ε))


;
; Reduction relation
;

(define k-cfa-red
  (reduction-relation
   k-cfa
   ; lookup
   (--> (name Σ
              ((label : v)
               ρ
               σ
               a
               t))
        (val
         ρ_h
         σ
         a
         u)
        (where a_v (lookup_env v ρ))
        (where (D ...) (lookup_sto a_v σ))
        (judgment-holds (deref (D ...)
                               (val ρ_h)))
        (where (D_κ ...) (lookup_sto a σ))
        (judgment-holds (deref (D_κ ...)
                               κ))
        (where u (tick Σ κ))
        lookup)
   ; add1
   (--> (name Σ
              ((label_1 : ((label_2 : add1)
                           e))
               ρ
               σ
               a
               t))
        (e
         ρ
         σ_new
         b
         u)
        (where (D ...) (lookup_sto a σ))
        (judgment-holds (deref (D ...)
                               κ))
        (where b (alloc Σ κ))
        (where u (tick Σ κ))
        (where σ_new (join ((b ((add1k a)))) σ))
        add1)
   ; app
   (--> (name Σ
              ((label : (e_0 e_1))
               ρ
               σ
               a
               t))
        (e_0
         ρ
         σ_new
         b
         u)
        (where (D ...) (lookup_sto a σ))
        (judgment-holds (deref (D ...)
                               κ))
        (where b (alloc Σ κ))
        (where u (tick Σ κ))
        (where σ_new (join ((b ((ar e_1 ρ a)))) σ))
        app)
   ; konts
   ;
   ; add1
   (--> (name Σ
              (atom
               ρ
               σ
               a
               t))
        ((add1-atom atom)
         ρ
         σ
         b
         u)
        (where (D ...) (lookup_sto a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (add1k b))))
        (where u (tick Σ κ))
        add1-kont)
   ; ar
   (--> (name Σ
              (lam
               ρ
               σ
               a
               t))
        (e
         ρ_ar
         σ_new
         b
         u)
        (where (D ...) (lookup_sto a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (ar e ρ_ar a_c))))
        (where b (alloc Σ κ))
        (where u (tick Σ κ))
        (where σ_new (join ((b ((fn lam ρ a_c)))) σ))
        ar-kont)
   ; fn
   (--> (name Σ
              (val
               ρ
               σ
               a
               t))
        (e
         ρ_fn_new
         σ_new
         c
         u)
        (where (D ...) (lookup_sto a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (fn (label : (λ (v) e))
                                         ρ_fn
                                         c))))
        (where b (alloc Σ κ))
        (where u (tick Σ κ))
        (where ρ_fn_new (insert_env v b ρ_fn))
        (where D_bind (make-D val ρ))
        (where σ_new (join ((b (D_bind))) σ))
        fn-kont)))

;
; Metafunctions
;
(define-metafunction k-cfa
  tick : Σ κ -> t
  ; lookup
  [(tick (ref ρ σ a t) κ)
   t]
  ; app
  [(tick ((label : (e_0 e_1)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; prim
  [(tick ((label : (prim e)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; ar
  [(tick (val ρ σ (label × contour_ar) contour) (ar e ρ_0 a_0))
   contour_ar]
  ; fn
  [(tick (val ρ σ a contour) (fn lam ρ_0 (label × contour_tail)))
   contour_tail]
  ; add1k
  [(tick (val ρ σ a contour) (add1k a_0))
   contour])


(define-metafunction k-cfa
  alloc : Σ κ -> a
  ; app
  [(alloc (name Σ ((label : (e_0 e_1)) ρ σ a contour))
          κ)
   ((e-label e_0) × (tick Σ κ))]
  ; prim
  [(alloc (name Σ ((label : (prim e)) ρ σ a contour))
          κ)
   ((e-label e) × contour)]
  ; ar
  [(alloc (name Σ (val ρ σ a contour))
          (name κ (ar e ρ_0 a_0)))
   ((e-label e) × (tick Σ κ))]
  ; fn
  [(alloc (name Σ (val ρ σ (label_a × contour_fn) contour))
          (name κ (fn (label : (λ (v) e)) ρ_0 a_0)))
   (v × contour_fn)])

(define-metafunction k-cfa
  make-D : val ρ -> D
  [(make-D atom ρ)
   atom]
  [(make-D lam ρ)
   (lam ρ)])

(define-metafunction k-cfa
  add1-atom : atom -> atom
  [(add1-atom (label : number))
   (label : ,(add1 (term number)))]
  [(add1-atom N)
   N])

(define-metafunction k-cfa
  k-left : contour -> contour
  [(k-left contour)
   contour_new
   (where contour_new (k-left-count ,k contour))])

(define-metafunction k-cfa
  k-left-count : natural contour -> contour
  [(k-left-count 0 contour)
   ε]
  [(k-left-count natural ε)
   ε]
  [(k-left-count natural (label contour))
   (label contour_tail)
   (where contour_tail (k-left-count ,(sub1 (term natural)) contour))])

(define-metafunction k-cfa
  e-label : e -> label
  [(e-label (label : v))
   label]
  [(e-label (label : (λ (v) e)))
   label]
  [(e-label (label : number))
   label]
  [(e-label (label : (e_0 e_1)))
   label]
  [(e-label (label : (prim e)))
   label])

(define-metafunction k-cfa
  prim-label : prim -> label
  [(prim-label (label : add1))
   label])

;;
; Env and sto helpers
;;
(define-metafunction k-cfa
  lookup_env : v ρ -> a
  [(lookup_env v ((v_1 a_1) ... (v a) (v_2 a_2) ...))
   a])

(define-metafunction k-cfa
  insert_env : v a ρ -> ρ
  [(insert_env v a ((v_1 a_1) ... (v a_old) (v_2 a_2) ...))
   ((v_1 a_1) ... (v a) (v_2 a_2) ...)]
  [(insert_env v a ((v_1 a_1) ...))
   ((v a) (v_1 a_1) ...)])

(define-metafunction k-cfa
  lookup_sto : a σ -> (D ...)
  [(lookup_sto a ((a_1 (D_1 ...)) ... (a (D ...)) (a_2 (D_2 ...)) ...))
   (D ...)])

(define-metafunction k-cfa
  merge : (D ...) -> (D ...)
  [(merge (D_1 ... const_1 D_2 ... const_2 D_3 ...))
   (merge (N D_1 ... D_2 ... D_3 ...))]
  [(merge (const_1 ... N const_2 ...))
   (N)]
  [(merge (D ...))
   (D ...)])

(define-metafunction k-cfa
  join : σ σ -> σ
  [(join σ_1 σ_2)
   ,(let ([h2 (make-hash (map (λ (x)
                                (cons (car x)
                                      (apply set (cadr x))))
                              (term σ_2)))])
      (for ([p (term σ_1)])
        (define k (car p))
        (define v (apply set (cadr p)))
        (hash-update! h2
                      k
                      (λ (v2)
                        (set-union v v2))
                      v))
      (map (λ (x)
             (list (car x)
                   (term (merge ,(set->list (cdr x))))))
           (sort (hash->list h2)
                 addr<?
                 #:key car)))])

; Comparison helpers
(define (contour->list c)
  (match c
    [`(,n ,c_tail)
     (cons n (contour->list c_tail))]
    ['ε '()]))

(check-equal? (contour->list 'ε) '())
(check-equal? (contour->list '(3 ε)) '(3))
(check-equal? (contour->list '(9 (2 ε))) '(9 2))

(define (num_list<? ls1 ls2)
  (define take_min (λ (ls) (take ls (min (length ls1) (length ls2)))))
  (define t1 (take_min ls1))
  (define t2 (take_min ls2))
  (and (not (= (length ls2) 0))
       (or (= (length ls1) 0)
           (andmap < t1 t2)
           (and (andmap = t1 t2)
                (< (length ls1)
                   (length ls2))))))

(check-equal? (num_list<? '(1) '()) #f)
(check-equal? (num_list<? '(3) '(1)) #f)
(check-equal? (num_list<? '(1) '(1 2)) #t)
(check-equal? (num_list<? '(2) '(1 2)) #f)
(check-equal? (num_list<? '(1 3) '(1 2)) #f)

(define (addr<? a1 a2)
  (match `(,a1 ,a2)
    [`((,(? symbol? x1) × ,c1) (,(? symbol? x2) × ,c2))
     (or (string<? (symbol->string x1)
                   (symbol->string x2))
         (num_list<? (contour->list c1) (contour->list c2)))]
    [`((,(? symbol?) × ,_) (,(? number?) × ,_))
     #t]
    [`((,(? number?) × ,_) (,(? symbol?) × ,_))
     #f]
    [`((,n1 × ,c1) (,n2 × ,c2))
     (or (< n1 n2)
         (num_list<? (contour->list c1) (contour->list c2)))]))

(check-equal? (addr<? '(1 × ε) '(2 × ε)) #t)
(check-equal? (addr<? '(1 × (2 ε)) '(2 × ε)) #t)
(check-equal? (addr<? '(1 × (2 ε)) '(1 × ε)) #f)
(check-equal? (addr<? '(1 × (3 ε)) '(1 × (2 ε))) #f)

;
; Judgment forms
;
(define-judgment-form k-cfa
  #:mode (deref I O)
  
  [-------------------------------
   (deref (D_1 ... atom D_2 ...) (atom ()))]
  [-------------------------------
   (deref (D_1 ... D D_2 ...) D)])


;
;; Church numerals.
;
(define (church-numeral n)
  (define (apply-n f n z)
    (cond
      [(= n 0) z]
      [else    `(,f ,(apply-n f (- n 1) z))]))
  (cond
    [(= n 0)   `(λ (f) (λ (z) z))]
    [else      `(λ (f) (λ (z) 
                         ,(apply-n 'f n 'z)))]))

(define SUM '(λ (n)
               (λ (m)
                 (λ (f)
                   (λ (z)
                     ((m f) ((n f) z)))))))
(define MUL '(λ (n)
               (λ (m)
                 (λ (f)
                   (λ (z)
                     ((m (n f)) z))))))

; Helper to check output value
; value -> (Σ -> bool)
(define (val-check value)
  (λ (x)
    (match (car x)
      [`(,_ : ,v)
       (eq? v value)]
      [_ #f])))

(apply-reduction-relation* k-cfa-red
                           (inject '((λ (f) (f (f 1)))
                                     (λ (x) (add1 x)))))

(apply-reduction-relation* k-cfa-red
                           (inject '((λ (f) ((f (λ (x) (add1 x)))
                                             (f 1)))
                                     (λ (x) x))))