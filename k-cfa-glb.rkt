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
     prim
     val
     ref
     (label : (begin e e e ...))
     (label : (if e e e))
     (label : (set! v e))
     (label : (e e ...))
     (label : (prim e))]
  [val ::=
       atom
       lam]
  [atom ::=
        (label : false)
        (label : number)]
  [lam (label : ulam)]
  [ulam (λ (v ...) e)]
  [prim ::=
        (label : add1)]
  [clo ::=
       (lam ρ)]
  [Storable ::=
            PS
            (κ κ ...)]
  [PS ::=
      number
      false
      N
      ∅
      (proc-with-arity natural natural ...)
      clo]
  [κ ::=
     (mt)
     (add1k a)
     (callk (e ...) ρ (PS ...) a)
     (setk a label c)
     (ifk e e ρ a)
     (begink e e ... a)]
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
    ; Transform let case while labeling.
    [`(let ([,v ,e] ...) ,e-body)
     (add-labels `((λ ,v ,e-body) ,@e) lab inc)]
    [`(if ,e0 ,e1 ,e2)
     (define-values (le0 c0) (add-labels e0 (inc lab) inc))
     (define-values (le1 c1) (add-labels e1 c0 inc))
     (define-values (le2 c2) (add-labels e2 c1 inc))
     (values `(,lab : (if ,le0 ,le1 ,le2))
             c2)]
    [`(begin ,e0 ,e1)
     (define-values (le0 c0) (add-labels e0 (inc lab) inc))
     (define-values (le1 c1) (add-labels e1 c0 inc))
     (values `(,lab : (begin ,le0 ,le1))
             c1)]
    [`(set! ,x ,e)
     (define-values (le c) (add-labels e (inc lab) inc))
     (values `(,lab : (set! ,x ,le))
             c)]
    [`(λ (,xs ...) ,e0)
     (define-values (le0 count) (add-labels e0 (inc lab) inc))
     (values `(,lab : (λ ,xs
                        ,le0))
             count)]
    [`(,es ...)
     (match-define (cons les-rev count)
       (foldl (λ (e acc)
                (match-define (cons les count) acc)
                (define-values (le c-new) (add-labels e count inc))
                (cons (cons le les) c-new))
              (cons '() (inc lab))
              es))
     (values `(,lab : ,(reverse les-rev))
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


(test-equal (labelFrom1 '((λ (x y) x)
                          1
                          2))
            '(1 : ((2 : (λ (x y) (3 : x))) (4 : 1) (5 : 2))))


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
         t))
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
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 κ))
        (where (b) (alloc Σ κ))
        (where u (tick Σ κ))
        (where σ_new (join_sto ((b ((add1k a)))) σ))
        add1)
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
        (where σ_new (join_sto ((b ((setk (lookup_env v ρ)
                                          label
                                          a))))
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
   ; add1
   (--> (name Σ
              (PS
               ρ
               σ
               a
               t))
        ((add1-PS PS)
         ρ
         σ
         b
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (add1k b))))
        (where u (tick Σ κ))
        add1-kont)
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
                                       (setk b label c))))
        (where u (tick Σ κ))
        setk)
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
        (e_body
         (join_env ,(map list (term (v_s ...)) (term (a_formals ...)))
                   ρ_clo)
         (join_sto ,(map list (term (a_formals ...)) (term (PS_args ... PS)))
                   σ)
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (callk ()
                                              ρ_k
                                              (((label : (λ (v_s ...) e_body))
                                                ρ_clo)
                                               PS_args ...)
                                              c))))
        (side-condition (eq? (length (term (v_s ...)))
                             (length (term (PS_args ... PS)))))
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
                                              (((label : (λ (v_s ...) e_body))
                                                ρ_clo)
                                               PS_args ...)
                                              c))))
        (side-condition (not (eq? (length (term (v_s ...)))
                                  (length (term (PS_args ... PS))))))
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
        ((if-chooser PS e_1 e_2)
         ρ_if
         σ
         c
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (ifk e_1 e_2 ρ_if c))))
        (where u (tick Σ κ)))
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
         (join_sto ((a ((begink (e_2 ...) c)))))
         a
         u)
        (judgment-holds (deref-κ (lookup_sto a σ)
                                 (name κ
                                       (begink (e_1 e_2 ...) c))))
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
  ; prim
  [(tick ((label : (prim e)) ρ σ a contour) κ)
   (k-left (label contour))]
  ; add1k
  [(tick (PS ρ σ a contour) (add1k a_0))
   contour]
  ; setk
  [(tick (PS ρ σ a contour) (setk b label c))
   contour]
  ; ifk
  [(tick (PS ρ σ (label × contour_ifk) contour) (ifk e_1 e_2 ρ_if c))
   contour_ifk]
  ; begink
  [(tick (PS ρ σ (label × contour_begink) contour) (begink e_1 e_2 ... c))
   contour_begink]
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
  ; prim
  [(alloc (name Σ ((label : (prim e)) ρ σ a contour))
          κ)
   (((e-label e) × contour))]
  ; call-more
  [(alloc (name Σ (PS ρ σ a contour))
          (name κ (callk (e_1 e_rest ...) ρ_k (PS_args ...) c)))
   (((e-label e_1) × (tick Σ κ)))]
  ; call-done
  [(alloc (name Σ (PS ρ σ a contour))
          (name κ
                (callk ()
                       ρ_k
                       (((label : (λ (v_s ...) e_body))
                         ρ_clo)
                        PS_args ...)
                       c)))
   ,(map (λ (formal)
           `(,formal × ,(term contour)))
         (term (v_s ...)))])



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

(define-metafunction k-cfa
  make-PS : val ρ -> PS
  [(make-PS atom ρ)
   ,(match (term atom)
      [`(,_ : ,x) x])]
  [(make-PS lam ρ)
   (lam ρ)])

(define-metafunction k-cfa
  val-env-pair : label PS ρ -> (val ρ)
  [(val-env-pair label clo ρ)
   clo]
  [(val-env-pair label PS ρ)
   ((label : PS) ρ)])

(define-metafunction k-cfa
  if-chooser : PS e e -> e
  [(if-chooser false e_1 e_2)
   e_2]
  [(if-chooser PS e_1 e_2)
   e_1])

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

(test-red '(let ([x 1]
                 [y 6])
             x)
          1)

(traces k-cfa-red
        (inject '(let [(x 3)]
                   (begin (set! x (λ (x) x))
                          ((add1 x))))))