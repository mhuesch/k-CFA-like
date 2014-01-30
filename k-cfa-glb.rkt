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
  [O ::=
     add1
     +
     o?]
  [clo ::=
       (lam ρ)]
  [Storable ::=
            PS
            (κ κ ...)]
  [PS ::=
      O
      atom
      B
      N
      ∅
      (proc-with-arity natural natural ...)
      clo]
  [o? ::=
      number?
      boolean?]
  [C ::=
     o?
     (-> C ... C)]
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
     (define le (add-labels e))
     `(,lab-current : (mon ,C ,le))]
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
         (let ([lab-2 (incLab!)])
           `(,lab-1 : (mon ,C (,lab-2 : ,s))))
         `(,lab-1 : ,s))]))

(define (O-contract s)
  (case s
    [(+) '(-> number? number? number?)]
    [(add1) '(-> number? number?)]
;    [(boolean?) '(-> any boolean?)]
;    [(number?) '(-> any boolean?)]
    [else #f]))

(check-equal? (labelFrom1 '(+ 1 2))
              '(1 : ((2 : (mon (-> number? number? number?) (3 : +)))
                     (4 : 1)
                     (5 : 2))))
(check-equal? (labelFrom1 '(mon (-> boolean? boolean?) (λ (x) x)))
              '(1 : (mon (-> boolean? boolean?)
                         (2 : (λ (x) (3 : x))))))
;(check-equal? (labelFrom1 '(boolean? ff))
;              '(1 : ((2 : (mon (-> any boolean?) (3 : boolean?)))
;                     (4 : ff))))
;(check-equal? (labelFrom1 '(number? 99))
;              '(1 : ((2 : (mon (-> any boolean?) (3 : number?)))
;                     (4 : 99))))
(check-equal? (labelFrom1 '((λ (x y) x)
                            1
                            2))
              '(1 : ((2 : (λ (x y) (3 : x))) (4 : 1) (5 : 2))))
                        

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
         ρ
         (join_sto ((d ((callk () ρ_k (o?) c)))
                    (c ((ifk PS (blame PS) ρ b)))) σ)
         d
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk o? ρ_k b))))
        (where (c d) (alloc Σ κ))
        (where u (tick Σ κ))
        chk-flat)
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        (,(add-labels `(λ ,(term (v_formals ...))
                         (mon ,(term C_res)
                              (,(term v)
                               ,@(map (λ (v C) `(mon ,C ,v))
                                      (term (v_formals ...))
                                      (term (C_args ...)))))))
         (join_env ((v c)) ρ)
         (join_sto ((c PS)) σ)
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (chk (-> C_args ... C_res) ρ_k b))))
        (where tt (proc? PS))
        (where v ,(fresh-var))
        (where (v_formals ...) ,(for/list ([i (range (length (term (C_args ...))))]) (fresh-var)))
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
                                       (chk (-> C_args ... C_res) ρ_k b))))
        (where ff (proc? PS))
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
        (where PS_result (O-helper O (PS_args ...)))
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
        (where string_error (O-helper O (PS_args ...)))
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
          (name κ (chk o? ρ_k b)))
   ,(let ([lab1 (incLab!)]
          [lab2 (incLab!)])
      (term ((,lab1 × (tick Σ κ)) (,lab2 × (tick Σ κ)))))]
  ; chk-arrow
  [(alloc (name Σ (PS ρ σ a t))
          (name κ (chk (-> C ...) ρ_k b)))
   ,(let ([lab1 (incLab!)])
      (term ((,lab1 × (tick Σ κ)))))]
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
(define (types-seen-set seen ts)
  (if (null? ts)
      seen
      (match (car ts)
        [(? number?)
         (types-seen-set (set-add seen 'number) (cdr ts))]
        ['N
         (types-seen-set (set-add seen 'N) (cdr ts))]
        ['∅
         (types-seen-set (set-add seen '∅) (cdr ts))]
        [else
         (types-seen-set (set-add seen 'other) (cdr ts))])))

(define (types-seen types)
  (sort (set->list (types-seen-set (set) types))
        string<=?
        #:key symbol->string))

(check-equal? (types-seen '(1 N))
              '(N number))
(check-equal? (types-seen '(1 N ∅))
              '(N number ∅))
(check-equal? (types-seen '(1 9 0))
              '(number))
(check-equal? (types-seen '(1 9 0))
              '(number))
(check-equal? (types-seen '(12 ((1 : (λ () (2 : 1))) ())))
              '(number other))

(define-metafunction k-cfa
  O-helper : O (PS ...) -> PS or string
  [(O-helper add1 (number))
   ,(add1 (term number))]
  [(O-helper add1 (N))
   N]
  [(O-helper add1 (∅))
   ∅]
  [(O-helper add1 (PS ...))
   ,(format "invalid application: ~s" (cons 'add1 (term (PS ...))))]
  [(O-helper + (PS ...))
   ,(case (types-seen (term (PS ...)))
      ['()
       0]
      [((number))
       (apply + (term (PS ...)))]
      [((N number) (N))
       'N]
      [((∅) (number ∅) (N number ∅) (N ∅))
       '∅]
      [else
       (format "invalid application: ~s" (term (PS ...)))])]
  [(O-helper number? (number)) tt]
  [(O-helper number? (N)) tt]
  [(O-helper number? (∅)) tt]
  [(O-helper number? (PS)) ff]
  [(O-helper boolean? (bool)) tt]
  [(O-helper boolean? (PS)) ff])

(test-equal (term (O-helper + ()))
            0)
(test-equal (term (O-helper + (N 3)))
            'N)
(test-equal (term (O-helper + (1 N ∅)))
            '∅)
(test-equal (term (O-helper +(1 9 0)))
            10)
(test-equal (term (O-helper + (12 ((1 : (λ () (2 : 1))) ()))))
            "invalid application: (12 ((1 : (λ () (2 : 1))) ()))")

(define-metafunction k-cfa
  proc? : PS -> bool
  [(proc? clo) tt]
  [(proc? O) tt]
  [(proc? PS) ff])

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
            '∅))


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
