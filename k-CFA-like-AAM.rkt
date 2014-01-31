#lang racket
(require redex)

(define k 10)

(define-language k-cfa
  [Σ (e ρ σ a t)]
  [ρ ((v a) ...)]
  [σ ((a (D ...)) ...)]
  [e ::=
     val
     (label : (e e))
     (label : (prim e))
     ref]
  [val ::=
       lam
       const]
  [lam (label : (λ (v) e))]
  [const (label : number)]
  [prim ::=
        (label : add1)]
  [D ::=
     (val ρ)
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
  [maybeLabel ::=
              label
              •]
  [labelOrVar ::=
              label
              v]
  [a b ::= (labelOrVar contour)]
  [t (maybeLabel contour)])

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

;; Takes an expression and annotates it with labels, and puts it in a starting Σ
(define (inject e)
  `(,(labelFrom1 e)
    ()
    (((0 ε) ((mt))))
    (0 ε)
    (• ε)))

(define (evaluate e)
  (apply-reduction-relation* k-cfa-red (inject e)))

(define (evaluate->val e)
  (let ([ret (evaluate e)])
    (match ret
      [(list `(,val ,_ ,_ 0 ,_))
       val]
      [_ (error "no reduced value: " ret)])))
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
               a_a
               t_t))
        (val
         ρ_h
         σ
         a_a
         t_u)
        (where a_v (lookup_env v ρ))
        (where (D ...) (lookup_sto a_v σ))
        (judgment-holds (deref (D ...)
                               (val ρ_h)))
        (where (D_κ ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D_κ ...)
                               κ))
        (where t_u (tick Σ κ))
        lookup)
   ; add1
   (--> (name Σ
              ((label_1 : ((label_2 : add1)
                           e))
               ρ
               σ
               a_a
               t_t))
        (e
         ρ
         σ_new
         a_b
         t_u)
        (where (D ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D ...)
                               κ))
        (where a_b (alloc Σ κ))
        (where t_u (tick Σ κ))
        (where σ_new (join a_b ((add1k a_a)) σ))
        add1)
   ; app
   (--> (name Σ
              ((label : (e_0 e_1))
               ρ
               σ
               a_a
               t_t))
        (e_0
         ρ
         σ_new
         a_b
         t_u)
        (where (D ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D ...)
                               κ))
        (where a_b (alloc Σ κ))
        (where t_u (tick Σ κ))
        (where σ_new (join a_b ((ar e_1 ρ a_a)) σ))
        app)
   ; konts
   ;
   ; add1
   (--> (name Σ
              ((label : number)
               ρ
               σ
               a_a
               t_t))
        ((label : ,(+ 1 (term number)))
         ρ
         σ
         a_c
         t_u)
        (where (D ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (add1k a_c))))
        (where t_u (tick Σ κ))
        add1-kont)
   ; ar
   (--> (name Σ
              (lam
               ρ
               σ
               a_a
               t_t))
        (e
         ρ_ar
         σ_new
         a_b
         t_u)
        (where (D ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (ar e ρ_ar a_c))))
        (where a_b (alloc Σ κ))
        (where t_u (tick Σ κ))
        (where σ_new (join a_b ((fn lam ρ a_c)) σ))
        ar-kont)
   ; fn
   (--> (name Σ
              (val
               ρ
               σ
               a_a
               t_t))
        (e
         ρ_fn_new
         σ_new
         a_c
         t_u)
        (where (D ...) (lookup_sto a_a σ))
        (judgment-holds (deref (D ...)
                               (name κ
                                     (fn (label : (λ (v) e))
                                         ρ_fn
                                         a_c))))
        (where a_b (alloc Σ κ))
        (where t_u (tick Σ κ))
        (where ρ_fn_new (insert_env v a_b ρ_fn))
        (where σ_new (join a_b ((val ρ)) σ))
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
  [(tick ((label : (e_0 e_1)) ρ σ a (maybeLabel contour)) κ)
   (label contour)]
  ; prim
  [(tick ((label : (prim e)) ρ σ a (maybeLabel contour)) κ)
   (label contour)]
  ; ar
  [(tick (val ρ σ a (maybeLabel contour)) (ar e ρ_0 a_0))
   (maybeLabel contour)]
  ; fn
  [(tick (val ρ σ a (label contour)) (fn lam ρ_0 a_0))
   (• (k-left (label contour)))]
  ; add1k
  [(tick (val ρ σ a (label contour)) (add1k a_0))
   (• (k-left (label contour)))])
    

(define-metafunction k-cfa
  alloc : Σ κ -> a
  ; app
  [(alloc ((label : (e_0 e_1)) ρ σ a (maybeLabel contour))
          κ)
   (label_e_0 contour)
   (where label_e_0 (e-label e_0))]
  ; prim
  [(alloc ((label : (prim e)) ρ σ a (maybeLabel contour))
          κ)
   (label_prim contour)
   (where label_prim (prim-label prim))]
  ; ar
  [(alloc (val ρ σ a (maybeLabel contour))
          (ar e ρ_0 a_0))
   (label contour)
   (where label (e-label e))]
  ; fn
  [(alloc (val ρ σ a (maybeLabel contour))
          (fn (label : (λ (v) e)) ρ_0 a_0))
   (v contour)])

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
    (where contour_tail (k-left-count ,(- (term natural) 1) contour))])

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


; σ σ -> σ
; sort, and remove duplicates
(define-metafunction k-cfa
  join : a (D ...) σ -> σ
  [(join a (D ...) ((a_1 (D_1 ...)) ... (a (D_2 ...)) (a_3 (D_3 ...)) ...))
   ((a_1 (D_1 ...)) ... (a (D ... D_2 ...)) (a_3 (D_3 ...)) ...)]
  [(join a (D ...) ((a_1 (D_1 ...)) ...))
   ((a (D ...)) (a_1 (D_1 ...)) ...)])


;
; Judgment forms
;
(define-judgment-form k-cfa
  #:mode (deref I O)
  
  [-------------------------------
   (deref (D_1 ... D D_2 ...) D)])







(traces k-cfa-red
        (inject '(((λ (x) x)
                   (λ (y) y))
                  (λ (z) z))))
