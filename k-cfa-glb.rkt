#lang racket
(require redex)
(require rackunit)

(define k 1)

(define-language k-cfa
  [eOrPS ::=
         e
         PS]
  [Σ ::=
     (eOrPS ρ σ a t)
     string]
  [ρ ((v a) ...)]
  [σ ((a Storable) ...)]
  [e ::=
     (blame any)
     val
     ref
     (label : O)
     (label : (begin e e e ...))
     (label : (if e e e))
     (label : (set! v e))
     (label : (e e ...))
     (label : (mon C e))]
  [val ::=
       labelAtom
       lam]
  [labelAtom ::=
             (label : atom)]
  [bool ::=
        tt
        ff]
  [atom ::=
        bool
        number]
  [lam (label : ulam)]
  [ulam (λ (v ...) e)]
  [clo ::=
       (lam ρ)]
  [O ::=
     add1
     +
     o?]
  [o? ::=
      number?
      boolean?]
  [C ::=
     any/c
     (label label : o?)
     (label label label label
            : label ..._1
            : label ..._1
            : (-> C ..._1 C))]
  [pred ::=
        o?
        any/c]
  [lattice-loc ::=
               top
               below]
  [Storable ::=
            PS
            (κ κ ...)]
  [PS :=
      sym
      O
      atom
      (proc-with-arity natural natural ...)
      clo]
  [sym ::=
       B
       N
       ∅]
  [κ ::=
     (mt)
     (add1k a)
     (callk (e ...) ρ (PS ...) a)
     (setk a c)
     (ifk eOrPS eOrPS ρ a)
     (begink e e ... a)
     (chk C ρ a)]
  [ref (label : v)]
  [v variable-not-otherwise-mentioned]
  [label natural]
  [contour ::=
           ε
           (label contour)]
  [labelOrVar ::=
              label
              v]
  [a b c d ::= (labelOrVar × contour)]
  [t u ::= contour])

(define (labelFrom1 e)
  (set! lab 1)
  (set! inc add1)
  (add-labels e))

(define-syntax-rule (incLab!)
  (begin0 lab
          (set! lab (inc lab))))

(define-syntax-rule (incLabList! n)
  (for/list ([_ (in-list (range n))]) (incLab!)))

(define lab null)
(define inc null)
(define (add-labels e)
  (match e
    ; Transform let case while labeling.
    [`(let ([,v ,e] ...) ,e-body)
     (add-labels `((λ ,v ,e-body) ,@e))]
    [`(if ,e0 ,e1 ,e2)
     (define lab-current (incLab!))
     (define le0 (add-labels e0))
     (define le1 (add-labels e1))
     (define le2 (add-labels e2))
     `(,lab-current : (if ,le0 ,le1 ,le2))]
    [`(begin ,es ...)
     (define lab-current (incLab!))
     (define les
       (reverse (foldl (λ (e acc)
                         (cons (add-labels e) acc))
                       '()
                       es)))
     `(,lab-current : (begin ,@les))]
    [`(set! ,x ,e)
     (define lab-current (incLab!))
     (define le (add-labels e))
     `(,lab-current : (set! ,x ,le))]
    [`(λ (,xs ...) ,e)
     (define lab-current (incLab!))
     (define le (add-labels e))
     `(,lab-current : (λ ,xs ,le))]
    [`(mon ,C ,e)
     (define lab-current (incLab!))
     (define lC (add-labels-C C))
     (define le (add-labels e))
     `(,lab-current : (mon ,lC ,le))]
    [`(,es ...)
     (define lab-current (incLab!))
     (define les
       (reverse (foldl (λ (e acc)
                         (cons (add-labels e) acc))
                       '()
                       es)))
     `(,lab-current : ,les)]
    [(? number? n)
     (define lab-current (incLab!))
     `(,lab-current : ,n)]
    [(? symbol? s)
     (define lab-1 (incLab!))
     (define C (O-contract s))
     (if C
         (let ([lC (add-labels-C C)]
               [lab-2 (incLab!)])
           `(,lab-1 : (mon ,lC
                           (,lab-2 : ,s))))
         `(,lab-1 : ,s))]))

(define (add-labels-C e)
  (match e
    [`(-> ,cs ...)
     (define lab-front (incLabList! 4))
     (define lab-mons (incLabList! (sub1 (length cs))))
     (define lab-formals (incLabList! (sub1 (length cs))))
     (define lCs
       (reverse (foldl (λ (c acc)
                         (cons (add-labels-C c) acc))
                       '()
                       cs)))
     `(,@lab-front : ,@lab-mons : ,@lab-formals : (-> ,@lCs))]
    ['any/c
     'any/c]
    [(? symbol? s)
     (define lab-1 (incLab!))
     (define lab-2 (incLab!))
     `(,lab-1 ,lab-2 : ,s)]))

(define (prefix-sym v)
  (string->symbol (format "_~s" v)))

(define-metafunction k-cfa
  prefix-vars : e -> e
  [(prefix-vars (label : v))
   (label : ,(prefix-sym (term v)))]
  [(prefix-vars (label : (begin e_s ...)))
   (label : (begin ,@(map (λ (e)
                            (term (prefix-vars ,e)))
                          (term (e_s ...)))))]
  [(prefix-vars (label : (if e_s ...)))
   (label : (if ,@(map (λ (e)
                         (term (prefix-vars ,e)))
                       (term (e_s ...)))))]
  [(prefix-vars (label : (set! v e)))
   (label : (set! ,(prefix-sym (term v)) (prefix-vars e)))]
  [(prefix-vars (label : (e_s ...)))
   (label : ,(map (λ (e)
                    (term (prefix-vars ,e)))
                  (term (e_s ...))))]
  [(prefix-vars (label : (mon C e)))
   (label : (mon C (prefix-vars e)))]
  ; catch-all
  [(prefix-vars e)
   e])

(define (O-contract s)
  (case s
    [(+) '(-> number? number? number?)]
    [(add1) '(-> number? number?)]
    [(boolean?) '(-> any/c boolean?)]
    [(number?) '(-> any/c boolean?)]
    [else #f]))

(check-equal? (labelFrom1 '(+ 1 2))
              '(1 : ((2 : (mon (3 4 5 6
                                  : 7 8
                                  : 9 10
                                  : (-> (11 12 : number?) (13 14 : number?) (15 16 : number?)))
                               (17 : +)))
                     (18 : 1)
                     (19 : 2))))
(check-equal? (labelFrom1 '(mon (-> boolean? boolean?) (λ (x) x)))
              '(1 : (mon (2 3 4 5
                            : 6
                            : 7
                            : (-> (8 9 : boolean?) (10 11 : boolean?)))
                         (12 : (λ (x) (13 : x))))))
(check-equal? (labelFrom1 '(mon any/c (add1 2)))
              '(1 : (mon any/c 
                         (2 : ((3 : (mon (4 5 6 7
                                            : 8
                                            : 9
                                            : (-> (10 11 : number?) (12 13 : number?))) (14 : add1)))
                               (15 : 2))))))
(check-equal? (labelFrom1 '((λ (x y) x)
                            1
                            2))
              '(1 : ((2 : (λ (x y) (3 : x))) (4 : 1) (5 : 2))))


;; Annotates a bar expression with labels and injects it into a starting Σ
(define (inject e)
  (term ((prefix-vars ,(labelFrom1 e))
         ()
         (((0 × ε) ((mt))))
         (0 × ε)
         ε)))


;
; Reduction relation
;

(define k-cfa-red
  (reduction-relation
   k-cfa
   #:domain Σ
   ; val -> PS
   (--> (name Σ
              (val
               ρ
               σ
               a
               t))
        ((make-PS val ρ)
         ρ
         σ
         a
         t)
        val-to-PS)
   ; labelled O (e) -> unlabeled O (PS)
   (--> (name Σ
              ((label : O)
               ρ
               σ
               a
               t))
        (O
         ρ
         σ
         a
         t)
        remove-O-label)
   ; mon
   (--> (name Σ
              ((label : (mon C e))
               ρ
               σ
               a
               t))
        (e
         ρ
         (join_sto ((b ((chk C ρ a))))
                   σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u(tick Σ κ))
        mon)
   ; lookup
   (--> (name Σ
              ((label : v)
               ρ
               σ
               a
               t))
        (PS
         ρ
         σ
         a
         u)
        (where a_v (lookup_env v ρ))
        (where PS (lookup_sto a_v σ))
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where u (tick Σ κ))
        lookup)
   ; set!
   (--> (name Σ
              ((label : (set! v e))
               ρ
               σ
               a
               t))
        (e
         ρ
         σ_new
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        (where σ_new (join_sto ((b ((setk (lookup_env v ρ) a))))
                               σ))
        set!)
   ; app
   (--> (name Σ
              ((label : (e_0 e_s ...))
               ρ
               σ
               a
               t))
        (e_0
         ρ
         (join_sto ((b ((callk (e_s ...) ρ () a)))) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        app)
   ; if
   (--> (name Σ
              ((label : (if e_0 e_1 e_2))
               ρ
               σ
               a
               t))
        (e_0
         ρ
         (join_sto ((b ((ifk e_1 e_2 ρ a)))) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        if)
   ; begin
   (--> (name Σ
              ((label : (begin e_0 e_1 e_2 ...))
               ρ
               σ
               a
               t))
        (e_0
         ρ
         (join_sto ((b ((begink e_1 e_2 ... a)))) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        begin)
   ; konts
   ;
   ; set!
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        ((lookup_sto b σ)
         ρ
         (join_sto ((b PS)) σ)
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (setk b c))))
        (where u (tick Σ κ))
        setk)
   ; chk
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (PS
         ρ_k
         σ
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk any/c ρ_k b))))
        (where u (tick Σ κ))
        chk-any/c)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (PS
         ρ
         (join_sto ((d ((callk () ρ_k (o?) c)))
                    (c ((ifk PS (blame PS) ρ b)))) σ)
         d
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk (label_1 label_2 : o?) ρ_k b))))
        (where (c d) (alloc Σ κ))
        (where u (tick Σ κ))
        chk-flat)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        ((label_1
          : (λ (v_formals ...)
              (label_2
               : (mon C_res
                      (label_3
                       : ((label_4 : v)
                          (label_mons : (mon C_args (label_formals : v_formals)))
                          ...))))))
         (join_env ((v c)) ρ)
         (join_sto ((c PS)) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk (label_1
                                             label_2
                                             label_3
                                             label_4
                                             : label_mons ...
                                             : label_formals ...
                                             : (-> C_args ... C_res)) ρ_k b))))
        (where tt (proc? PS ,(length (term (C_args ...)))))
        (where v ,(fresh-var))
        (where (v_formals ...) ,(for/list ([_ (in-list (term (C_args ...)))]) (fresh-var)))
        (where (c) (alloc Σ κ))
        (where u (tick Σ κ))
        chk-arrow-proc)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        ((blame PS)
         ρ
         σ
         a
         t)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk (label_1
                                             label_2
                                             label_3
                                             label_4
                                             : label_mons ...
                                             : label_formals ...
                                             : (-> C_args ... C_res)) ρ_k b))))
        (where ff (proc? PS ,(length (term (C_args ...)))))
        chk-arrow-not-proc)
   ; call
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (e_1
         ρ_k
         (join_sto ((b ((callk (e_rest ...) ρ_k (PS_args ... PS) c)))) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk (e_1 e_rest ...) ρ_k (PS_args ...) c))))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        callk-more)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (PS_result
         ρ_k
         σ
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk ()
                                              ρ_k
                                              (PS_k ...)
                                              c))))
        (where (O PS_args ...)
               (PS_k ... PS))
        (where PS_result (O-guard O (PS_args ...)))
        (where u (tick Σ κ))
        callk-done-O-success)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        string_error
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk ()
                                              ρ_k
                                              (PS_k ...)
                                              c))))
        (where (O PS_args ...)
               (PS_k ... PS))
        (where string_error (O-guard O (PS_args ...)))
        (where u (tick Σ κ))
        callk-done-O-error)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (e_body
         (join_env ,(map list (term (v_s ...)) (term (a_formals ...)))
                   ρ_clo)
         (join_sto ,(map list (term (a_formals ...)) (term (PS_args ...)))
                   σ)
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk ()
                                              ρ_k
                                              (PS_k ...)
                                              c))))
        (where (((label : (λ (v_s ...) e_body))
                 ρ_clo)
                PS_args ...)
               (PS_k ... PS))
        (side-condition (eq? (length (term (v_s ...)))
                             (length (term (PS_args ...)))))
        (where (a_formals ...) (alloc Σ κ))
        (where u (tick Σ κ))
        callk-done-clo-arity-correct)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        "arity error"
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk ()
                                              ρ_k
                                              (PS_k ...)
                                              c))))
        (where (((label : (λ (v_s ...) e_body))
                 ρ_clo)
                PS_args ...)
               (PS_k ... PS))
        (side-condition (not (eq? (length (term (v_s ...)))
                                  (length (term (PS_args ...))))))
        (where (a_formals ...) (alloc Σ κ))
        (where u (tick Σ κ))
        callk-done-clo-arity-incorrect)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (∅
         ρ
         σ
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk () ρ ((proc-with-arity natural ...) PS_args ...) c))))
        (side-condition (member (add1 (length (term (PS_args ...))))
                                (term (natural ...))))
        (where u (tick Σ κ))
        callk-proc-with-arity-correct)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        "arity error"
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk () ρ ((proc-with-arity natural ...) PS_args ...) c))))
        (side-condition (not (member (add1 (length (term (PS_args ...))))
                                     (term (natural ...)))))
        (where u (tick Σ κ))
        callk-proc-with-arity-incorrect)
   ; if
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        ((if-chooser PS eOrPS_1 eOrPS_2)
         ρ_if
         σ
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (ifk eOrPS_1 eOrPS_2 ρ_if c))))
        (where u (tick Σ κ))
        ifk)
   ; begin
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (e_1
         ρ
         σ
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (begink e_1 c))))
        (where u (tick Σ κ))
        begin-done)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (e_1
         ρ
         (join_sto ((b ((begink e_2 e_3 ... c))))
                   σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (begink e_1 e_2 e_3 ... c))))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        begin-more)))
;
; Metafunctions
;
(define-metafunction k-cfa
  tick : Σ κ -> t
  ; lookup
  [(tick (ref ρ σ a t) κ)
   t]
  ; begin
  [(tick ((label : (begin e_0 e_1 e_2 ...)) ρ σ a t) κ)
   t]
  ; app
  [(tick ((label : (e_0 e_s ...)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; if
  [(tick ((label : (if e_0 e_1 e_2)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; set!
  [(tick (name Σ ((label : (set! v e)) ρ σ a contour)) κ)
   (k-left (label contour))]
  ; O
  [(tick ((label : (O e)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; mon
  [(tick ((label : (mon C e)) ρ σ a t) κ)
   (k-left (label t))]
  ; add1k
  [(tick (PS ρ σ a contour) (add1k a_0))
   contour]
  ; setk
  [(tick (PS ρ σ a contour) (setk b c))
   contour]
  ; ifk
  [(tick (PS ρ σ (label × contour_ifk) contour) (ifk eOrPS_1 eOrPS_2 ρ_if c))
   contour_ifk]
  ; begink
  [(tick (PS ρ σ (label × contour_begink) contour) (begink e_1 e_2 ... c))
   contour_begink]
  ; chk
  [(tick (PS ρ σ (label × contour_chk) t) (chk C ρ_k b))
   contour_chk]
  ; callk-more
  [(tick (PS ρ σ (label × contour_callk) contour) (callk (e_k ...) ρ_k (PS_k ...) a))
   contour_callk])


(define-metafunction k-cfa
  alloc : Σ κ -> (a ...)
  ; app
  [(alloc (name Σ ((label : (e_0 e_s ...)) ρ σ a contour))
          κ)
   (((e-label e_0) × (tick Σ κ)))]
  ; if
  [(alloc (name Σ ((label : (if e_0 e_1 e_2)) ρ σ a t))
          κ)
   (((e-label e_0) × (tick Σ κ)))]
  ; begin
  [(alloc (name Σ ((label : (begin e_0 e_1 e_2 ...)) ρ σ a t))
          κ)
   (((e-label e_0) × (tick Σ κ)))]
  ; set!
  [(alloc (name Σ ((label_1 : (set! v e)) ρ σ a contour))
          κ)
   (((e-label e) × (tick Σ κ)))]
  ; mon
  [(alloc (name Σ ((label_1 : (mon C e)) ρ σ a t))
          κ)
   (((e-label e) × (tick Σ κ)))]
  ; begink
  [(alloc (name Σ (PS ρ σ a contour))
          (name κ (begink e_1 e_2 ... b)))
   (((e-label e_1) × (tick Σ κ)))]
  ; chk-flat
  [(alloc (name Σ (PS ρ σ a t))
          (name κ (chk (label_1 label_2 : o?) ρ_k b)))
   ((label_1 × (tick Σ κ)) (label_2 × (tick Σ κ)))]
  ; chk-arrow
  [(alloc (name Σ (PS ρ σ a t))
          (name κ (chk (label_1 label_s ...
                                : label_mons ...
                                : label_formals ...
                                : (-> C_args ... C_res)) ρ_k b)))
   ((label_1 × (tick Σ κ)))]
  ; call-more
  [(alloc (name Σ (PS ρ σ a contour))
          (name κ (callk (e_1 e_rest ...) ρ_k (PS_args ...) c)))
   (((e-label e_1) × (tick Σ κ)))]
  ; call-done
  [(alloc (name Σ (PS ρ σ a contour))
          (name κ
                (callk ()
                       ρ_k
                       (PS_k ...)
                       c)))
   ,(map (λ (formal)
           `(,formal × ,(term contour)))
         (term (v_s ...)))
   (where (((label : (λ (v_s ...) e_body))
            ρ_clo)
           PS_args ...)
          (PS_k ... PS))])

; O helpers
(define-metafunction k-cfa
  O-guard : O (PS ...) -> PS or string
  ; "top" of lattice - happy path
  [(O-guard O (PS ...))
   (O-helper O (PS ...))
   (where (-> pred_args ... pred_res) ,(O-contract (term O)))
   (side-condition (eq? (length (term (pred_args ...)))
                        (length (term (PS ...)))))
   (where (top ...) ,(map (λ (p v) (term (check-arg ,p ,v))) (term (pred_args ...)) (term (PS ...))))]
  ; "below" value on lattice - o?
  [(O-guard o? (PS ...))
   (O-helper o? (PS ...))
   (where (-> pred_args ... pred_res) ,(O-contract (term o?)))
   (side-condition (eq? (length (term (pred_args ...)))
                        (length (term (PS ...)))))
   (where (lattice-loc ...) ,(map (λ (p v) (term (check-arg ,p ,v))) (term (pred_args ...)) (term (PS ...))))]
  ; "below" value on lattice - O
  [(O-guard O (PS ...))
   (contract->type pred_res)
   (where (-> pred_args ... pred_res) ,(O-contract (term O)))
   (side-condition (eq? (length (term (pred_args ...)))
                        (length (term (PS ...)))))
   (where (lattice-loc ...) ,(map (λ (p v) (term (check-arg ,p ,v))) (term (pred_args ...)) (term (PS ...))))]
  ; arity mismatch
  [(O-guard O (PS ...))
   ,(format "arity error in ~s" (term (O PS ...)))
   (where (-> pred_args ... pred_res) ,(O-contract (term O)))
   (side-condition (not (eq? (length (term (pred_args ...)))
                             (length (term (PS ...))))))])

; Happy path implementations
(define-metafunction k-cfa
  O-helper : O (PS ...) -> PS
  [(O-helper add1 (number))
   ,(add1 (term number))]
  [(O-helper + (number ...))
   ,(apply + (term (number ...)))]
  [(O-helper number? (number)) tt]
  [(O-helper number? (N)) tt]
  [(O-helper number? (∅)) tt]
  [(O-helper number? (PS)) ff]
  [(O-helper boolean? (bool)) tt]
  [(O-helper boolean? (PS)) ff])

(define-metafunction k-cfa
  check-arg : pred PS -> lattice-loc
  [(check-arg number? number) top]
  [(check-arg number? N) below]
  [(check-arg number? ∅) below]
  [(check-arg boolean? bool) top]
  [(check-arg boolean? B) below]
  [(check-arg boolean? ∅) below]
  [(check-arg any/c N) below]
  [(check-arg any/c B) below]
  [(check-arg any/c ∅) below]
  [(check-arg any/c PS) top])

(define-metafunction k-cfa
  contract->type : pred -> sym
  [(contract->type number?) N]
  [(contract->type number?) B]
  [(contract->type number?) ∅])

(check-equal? (term (O-guard + (1 2)))
              (term 3))
(check-equal? (term (O-guard + (1 2 3)))
              (term "arity error in (+ 1 2 3)"))
(check-equal? (term (O-guard + (1 N)))
              (term N))
(check-equal? (term (O-guard number? (1 N)))
              (term "arity error in (number? 1 N)"))
(check-equal? (term (O-guard number? (N)))
              (term tt))
(check-equal? (term (O-guard boolean? (N)))
              (term ff))



  

(define-metafunction k-cfa
  proc? : PS natural -> bool
  [(proc? ((label : (λ (v ...) e)) ρ) natural)
   ,(if (= (term natural) (length (term (v ...))))
        (term tt)
        (term ff))]
  [(proc? add1 1) tt]
  [(proc? + 2) tt]
  [(proc? o? 1) tt]
  [(proc? PS natural) ff])

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

; Misc helpers
;
(define fresh-count 0)
(define (fresh-var)
  (begin0
    (string->symbol (format "var_~s" fresh-count))
    (set! fresh-count (add1 fresh-count)))) 

(define-metafunction k-cfa
  make-PS : val ρ -> PS
  [(make-PS (label : atom) ρ)
   atom]
  [(make-PS lam ρ)
   (lam ρ)])

(define-metafunction k-cfa
  val-env-pair : label PS ρ -> (val ρ)
  [(val-env-pair label clo ρ)
   clo]
  [(val-env-pair label PS ρ)
   ((label : PS) ρ)])

(define-metafunction k-cfa
  if-chooser : PS eOrPS eOrPS -> eOrPS
  [(if-chooser ff eOrPS_1 eOrPS_2)
   eOrPS_2]
  [(if-chooser PS eOrPS_1 eOrPS_2)
   eOrPS_1])

(define-metafunction k-cfa
  add1-PS : PS -> PS
  [(add1-PS number)
   ,(add1 (term number))]
  [(add1-PS ∅)
   ∅]
  [(add1-PS N)
   N])

(define-metafunction k-cfa
  e-label : e -> label
  [(e-label e)
   ,(match (term e)
      [`(,label : ,_)
       label])])
;;
; Env and sto helpers
;;
(define-metafunction k-cfa
  lookup_env : v ρ -> a
  [(lookup_env v ((v_1 a_1) ... (v a) (v_2 a_2) ...))
   a])

(define-metafunction k-cfa
  lookup_sto : a σ -> Storable
  [(lookup_sto a ((a_1 Storable_1) ... (a Storable) (a_2 Storable_2) ...))
   Storable])

(define-metafunction k-cfa
  clo-get-arity : clo -> natural
  [(clo-get-arity ((label : (λ (v ...) e)) ρ))
   ,(length (term (v ...)))])

(define(string-format<? a1 a2)
  (string<? (format "~s" a1)
            (format "~s" a2)))

(check-equal? (string-format<? 'z 'x) #f)
(check-equal? (string-format<? '(1 × ε) '(2 × ε)) #t)
(check-equal? (string-format<? '(1 × (2 ε)) '(2 × ε)) #t)
(check-equal? (string-format<? '(1 × (2 ε)) '(1 × ε)) #t)
(check-equal? (string-format<? '(1 × (3 ε)) '(1 × (2 ε))) #f)


(define-metafunction k-cfa
  join_env : ρ ρ -> ρ
  [(join_env ρ_1 ρ_2)
   ,(let ([h2 (make-hash (term ρ_2))])
      (for ([p (term ρ_1)])
        (define v (car p))
        (define a (cdr p))
        (hash-set! h2 v a))
      (sort (hash->list h2)
            string-format<?
            #:key car))])

(test-equal (term (join_env ((y (y × (2 (1 ε)))) (z (z × ε)))
                            ((x (x × (97 ε))) (y (y × (4 (1 ε)))))))
            (term ((x (x × (97 ε))) (y (y × (2 (1 ε)))) (z (z × ε)))))

(define-metafunction k-cfa
  glb : PS PS -> PS
  ; Equal
  [(glb PS_1 PS_1)
   PS_1]
  ; Bools
  [(glb bool_1 bool_2)
   B]
  [(glb B bool)
   B]
  [(glb bool B)
   B]
  ; Numbers
  [(glb number_1 number_2)
   N]
  [(glb number N)
   N]
  [(glb N number)
   N]
  ; Closures
  [(glb clo_1 clo_2)
   (proc-with-arity ,@(remove-duplicates (list (term (clo-get-arity clo_1))
                                               (term (clo-get-arity clo_2)))))]
  [(glb clo (proc-with-arity natural ...))
   (proc-with-arity ,@(remove-duplicates (apply list
                                                (term (clo-get-arity clo))
                                                (term (natural ...)))))]
  ; Catch-all
  [(glb PS_1 PS_2)
   ∅])

(test-equal (term (glb 1 1))
            (term 1))

(define-metafunction k-cfa
  storableJoin : Storable Storable -> Storable
  ; call glb
  [(storableJoin PS_1 PS_2)
   (glb PS_1 PS_2)]
  ; Union konts
  [(storableJoin (κ_1 ...) (κ_2 ...))
   ,(remove-duplicates (append (term (κ_1 ...))
                               (term (κ_2 ...))))])

(define-metafunction k-cfa
  join_sto : σ σ -> σ
  [(join_sto σ_1 σ_2)
   ,(let ([h2 (make-hash (map (λ (x)
                                (cons (car x)
                                      (cadr x)))
                              (term σ_2)))])
      (for ([p (term σ_1)])
        (define k (car p))
        (define s1 (cadr p))
        (hash-update! h2
                      k
                      (λ (s2)
                        (term (storableJoin ,s1 ,s2)))
                      s1))
      (map (λ (x)
             (list (car x)
                   (cdr x)))
           (sort (hash->list h2)
                 string-format<?
                 #:key car)))])

;
; Judgment forms
;
(define-judgment-form k-cfa
  #:mode (deref-κ I O)
  
  [-------------------------------
   (deref-κ (κ_1 ... κ κ_2 ...) κ)])


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



; Tests
(define (test-red exp PS)
  (match (apply-reduction-relation* k-cfa-red
                                    (inject exp))
    ['()
     (print (format "Could not reduce: ~s" exp))]
    [l
     (test-not-false (format "~s" `(member ,PS ,(map car l)))
                     (member PS (map (λ (x)
                                       (match x
                                         [(? string?)
                                          x]
                                         [(? pair?)
                                          (car x)]))
                                     l)))]))

(define (test-red-error exp PS)
  (match (apply-reduction-relation* k-cfa-red
                                    (inject exp))
    ['()
     (print (format "Could not reduce: ~s" exp))]
    [l
     (test-not-false (format "~s" `(member ,PS ,l))
                     (member PS l))]))

(define (run-tests)
  (test-red '(+ 1 2)
            3)
  
  (test-red '(mon boolean? 1)
            '(blame 1))
  
  (test-red '((mon (-> number? number?)
                   3)
              2)
            '(blame 3))
  
  (test-red '((mon (-> (-> number? (-> boolean? number?))
                       boolean?)
                   (λ (f) (number? ((f 5) tt))))
              (λ (n) (λ (b) (if b (+ n 200) ff))))
            'tt)
  
  (test-red '(if 3
                 1
                 2)
            1)
  
  (test-red-error '((λ (x) (begin (set! x (λ (y) y))
                                  (x 1 2)))
                    (λ (z) z))
                  "arity error")
  
  
  (test-red '((λ (x) (begin (set! x 1)
                            x))
              2)
            'N)
  
  (test-red '(let ([x 1]
                   [y 6])
               x)
            1)
  
  (test-red-error '((λ (x) 1))
                  "arity error")
  
  (test-red '((λ (x) (begin (set! x 1)
                            (+ x 3)))
              2)
            'N)
  
  (test-red '((λ (x) (begin (set! x (λ () 1))
                            (+ x 3)))
              2)
            'N))


#|
(test-red `((,(church-numeral 2)
             (λ (x)
               (add1 x)))
            0)
          2)

(test-red `((((,MUL
               ,(church-numeral 1))
              ,(church-numeral 4))
             (λ (x)
               (add1 x)))
            0)
          '∅)

(traces k-cfa-red
        (inject '(let [(x 3)]
                   (begin (set! x (λ (x) x))
                          (add1 x)))))
|#
