(load "mk.scm")
(load "matche.scm")
(load "pmatch.scm")
(load "test-check.scm")

;; High-level thoughts:
;;
;; Ideally, not-in-envo would be a constraint.  Then, the lambda
;; clause would not be recursive.
;;
;; shape constraints or types would be awesome I think
;;
;; There are 6 ways to order the recursive calls in the application
;; clause of eval-expo.  There is no ideal ordering of these
;; clauses--it depends on the groundness of exp, env, and val.
;; Ideally all 6 orderings should be run in parallel.  Or, each
;; ordering could be run for an n-second time-out that doubled each
;; run, or whatever, until one ordering succeeded.  Or, maybe use a
;; Mercury-style approach, in which groundness of arguments at runtime
;; results in calls to versions of eval-expo with different orderings
;; of recursive calls.

;; Writing/explanatory thoughts:
;;
;; Need to make clear difference between translating to miniKanren
;; Scheme predicates vs. Scheme functions that return non-boolean
;; values.

(define lookup-tests
  (lambda (lookup)

    (test "lookup-1"
      (lookup 'z '((z . 5)))
      5)

    (test "lookup-2"
      (lookup 'z '((z . 5) (z . 6)))
      5)

    (test "lookup-3"
      (lookup 'z '((w . 7) (z . 5) (z . 6)))
      5)
    
    ))


;; cond clauses can't be reordered
(define lookup
  (lambda (x env)
    (pmatch env
      (() (error 'lookup "unbound variable"))
      (((,y . ,v) . ,rest)
       (cond
         ((eq? y x) v)
         (else (lookup x rest)))))))

(printf " *** lookup 1\n")
(lookup-tests lookup)


;; better definition:
;; check that x and y are indeed symbols, and
;; can reorder clauses.  Also arguably cleaner stylistically,
;; since not mixing pmatch and cond unnecessarily
(define lookup
  (lambda (x env)
    (unless (symbol? x)
      (error 'lookup "first argument must be a symbol"))
    (pmatch env
      (() (error 'lookup "unbound variable"))
      (((,y . ,v) . ,rest) (guard (symbol? y) (eq? y x))
       v)
      (((,y . ,v) . ,rest) (guard (symbol? y) (not (eq? y x)))
       (lookup x rest)))))

(printf " *** lookup 2\n")
(lookup-tests lookup)


;; This definition does *not* work, since the 'x' in the second clause
;; shadows the first argument to 'lookup'
(define lookup
  (lambda (x env)
    (unless (symbol? x)
      (error 'lookup "first argument must be a symbol"))
    (pmatch env
      (() (error 'lookup "unbound variable"))
      (((,x . ,v) . ,rest)
       v)
      (((,y . ,v) . ,rest) (guard (symbol? y) (not (eq? y x)))
       (lookup x rest)))))

(printf " *** lookup 3\n")
(printf "*** incorrect lookup (should fail)\n")
(lookup-tests lookup)


;; show lookup still works with clauses reordered
(define lookup
  (lambda (x env)
    (unless (symbol? x)
      (error 'lookup "first argument must be a symbol"))
    (pmatch env
      (((,y . ,v) . ,rest) (guard (symbol? y) (not (eq? y x)))
       (lookup x rest))
      (((,y . ,v) . ,rest) (guard (symbol? y) (eq? y x))
       v)
      (() (error 'lookup "unbound variable")))))

(printf " *** lookup 4\n")
(lookup-tests lookup)



;; These definitions are ugly, since they combine pmatch with cond

(let ()

  (define lookup
    (lambda (x env)
      (unless (symbol? x)
        (error 'lookup "first argument must be a symbol"))
      (pmatch env
        (() (error 'lookup "unbound variable"))
        (((,y . ,v) . ,rest) (guard (symbol? y))
         (cond
           ((eq? y x) v)
           ((not (eq? y x))
            (lookup x rest)))))))

  (printf " *** lookup 5\n")
  (lookup-tests lookup)

  )

;; show lookup still works with clauses reordered
(let ()
  
  (define lookup
    (lambda (x env)
      (unless (symbol? x)
        (error 'lookup "first argument must be a symbol"))
      (pmatch env
        (((,y . ,v) . ,rest) (guard (symbol? y))
         (cond
           ((not (eq? y x))
            (lookup x rest))
           ((eq? y x) v)))
        (() (error 'lookup "unbound variable")))))

  (printf " *** lookup 6\n")
  (lookup-tests lookup)

  )


(define lookupo-tests
  (lambda (lookupo)

    (test "lookupo-1"
      (run* (q) (lookupo 'z '((z . 5) (z . 6)) q))
      '(5))

    (test "lookupo-2"
      (run* (q) (lookupo 'z '((w . 7) (z . 5) (z . 6)) q))
      '(5))

    (test "lookupo-3"
      (run* (q) (lookupo 'y '((x . foo) (y . bar)) q))
      '(bar))

    (test "lookupo-4"
      (run* (q) (lookupo 'w '((x . foo) (y . bar)) q))
      '())

    (test "lookupo-5"
      (run 5 (q) (lookupo 'z q 5))
      '(((z . 5) . _.0)
        (((_.0 . _.1) (z . 5) . _.2)
         (=/= ((_.0 z))) (sym _.0))
        (((_.0 . _.1) (_.2 . _.3) (z . 5) . _.4)
         (=/= ((_.0 z)) ((_.2 z))) (sym _.0 _.2))
        (((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (z . 5) . _.6)
         (=/= ((_.0 z)) ((_.2 z)) ((_.4 z))) (sym _.0 _.2 _.4))
        (((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (z . 5) . _.8)
         (=/= ((_.0 z)) ((_.2 z)) ((_.4 z)) ((_.6 z))) (sym _.0 _.2 _.4 _.6))))
    
    ))


(define lookupo
  (lambda (x env val)
    (fresh ()
      (symbolo x)
      (matche env
        (((,y . ,v) . ,rest) (symbolo y)
         (== y x) (== v val))
        (((,y . ,v) . ,rest) (symbolo y)
         (=/= y x) (lookupo x rest val))))))

(lookupo-tests lookupo)


;; show lookupo works with reordered clauses
(define lookupo
  (lambda (x env val)
    (fresh ()
      (symbolo x)
      (matche env
        (((,y . ,v) . ,rest) (symbolo y)
         (=/= y x) (lookupo x rest val))
        (((,y . ,v) . ,rest) (symbolo y)
         (== y x) (== v val))))))

(lookupo-tests lookupo)


;; shorter definition, but which doesn't doesn't correspond with the pmatch version as well
(let ()

  (defmatche (lookupo x env val)
    ((,x ((,x . ,val) . ,rest) ,val)
     (symbolo x))
    ((,x ((,y . ,v) . ,rest) ,val)
     (symbolo x) (symbolo y)
     (=/= x y)
     (lookupo x rest val)))

  (lookupo-tests lookupo)

  )

;; shorter definition, with defmatch clauses swapped.
(let ()

  (defmatche (lookupo x env val)
    ((,x ((,y . ,v) . ,rest) ,val)
     (symbolo x) (symbolo y)
     (=/= x y)
     (lookupo x rest val))
    ((,x ((,x . ,val) . ,rest) ,val)
     (symbolo x)))

  (lookupo-tests lookupo)

  )


#|
;; These definitions are ugly, since they combine matche with conde

(define lookupo
  (lambda (x env val)
    (fresh ()
      (symbolo x)
      (matche env
        (((,y . ,v) . ,rest) (symbolo y)
         (conde
           ((== y x) (== v val))
           ((=/= y x)
            (lookupo x rest val))))))))

(lookupo-tests lookupo)

;; show lookupo works with reordered clauses
(define lookupo
  (lambda (x env val)
    (fresh ()
      (symbolo x)
      (matche env
        (((,y . ,v) . ,rest) (symbolo y)
         (conde
           ((=/= y x)
            (lookupo x rest val))
           ((== y x) (== v val))))))))

(lookupo-tests lookupo)
|#



(define big-omega
  '((lambda (lambda) (lambda lambda))
    (lambda (lambda) (lambda lambda))))


(define eval-exp-tests
  (lambda (eval-exp)

    (test "eval-exp-1"
      (eval-exp
       '(((lambda (x)
            (lambda (y) x))
          (lambda (z) z))
         (lambda (a) a))
       '())
      '(closure z z ()))

    (test "eval-exp-2"
      (eval-exp
       '((lambda (x)
           (lambda (y) x))
         (lambda (z) z))
       '())
      '(closure y x ((x . (closure z z ())))))

    (test "eval-exp-3"
      (eval-exp
       '((lambda (z)
           ((lambda (z)
              z)
            (lambda (w) w)))
         (lambda (v) v))
       '())
      '(closure w w ((z closure v v ()))))

    ;; This is the "easy" shadowing test, which doesn't require
    ;; not-in-env to work properly.
    (test "eval-exp-shadow-lambda-1"
      (eval-exp '((lambda (lambda)
                    (lambda lambda))
                  (lambda (w) w)) '())
      '(closure w w ()))
    
    ))



;; CBV lambda calculus, shadowing of lambda handled improperly
;; Schemely version
(define eval-exp
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x))
       (lookup x env))
      ((lambda (,x) ,body) (guard (symbol? x))
       `(closure ,x ,body ,env))
      ((,rator ,rand)
       (let ((proc (eval-exp rator env))
             (arg (eval-exp rand env)))
         (pmatch proc
           ((closure ,x ,body ,env2) (guard (symbol? x))
            (eval-exp body `((,x . ,arg) . ,env2)))))))))

(eval-exp-tests eval-exp)

;; Show that this definition of eval-exp doesn't handle shadowing of
;; lambda properly.

(test "eval-expo-broken-shadowing-of-lambda"
  (eval-exp
   '((lambda (lambda)
       (lambda (x) x))
     (lambda (w) w))
   '())
  'should-signal-an-error)

(define not-in-env-tests
  (lambda (not-in-env)

    (test "not-in-env-1"
      (not-in-env 'z '())
      #t)

    (test "not-in-env-2"
      (not-in-env 'z '((w . 5)))
      #t)

    (test "not-in-env-3"
      (not-in-env 'z '((z . 5)))
      #f)

    (test "not-in-env-4"
      (not-in-env 'z '((w . 6) (z . 5)))
      #f)
    
    (test "not-in-env-5"
      (not-in-env 'z '((w . 6) (v . 5)))
      #t)
        
    ))

(define not-in-env
  (lambda (x env)
    (symbol? x)
    (pmatch env
      (() #t)
      (((,y . ,v) . ,rest) (guard (symbol? y))
       (cond
         ((eq? y x) #f)
         ((not (eq? y x))
          (not-in-env x rest)))))))

(not-in-env-tests not-in-env)

(define not-in-envo-tests
  (lambda (not-in-envo)

    (test "not-in-envo-1"
      (run* (q)
        (not-in-envo 'z '()))
      '(_.0))

    (test "not-in-envo-2"
      (run* (q)
        (not-in-envo 'z '((w . 5))))
      '(_.0))

    (test "not-in-envo-3"
      (run* (q)
        (not-in-envo 'z '((z . 5))))
      '())

    (test "not-in-envo-4"
      (run* (q)
        (not-in-envo 'z '((w . 6) (z . 5))))
      '())
    
    (test "not-in-envo-5"
      (run* (q)
        (not-in-envo 'z '((w . 6) (v . 5))))
      '(_.0))

    (test "not-in-envo-6"
      (run 5 (q)
        (not-in-envo 'z q))
      '(()
        (((_.0 . _.1))
         (=/= ((_.0 z)))
         (sym _.0))
        (((_.0 . _.1) (_.2 . _.3))
         (=/= ((_.0 z)) ((_.2 z)))
         (sym _.0 _.2))
        (((_.0 . _.1) (_.2 . _.3) (_.4 . _.5))
         (=/= ((_.0 z)) ((_.2 z)) ((_.4 z)))
         (sym _.0 _.2 _.4))
        (((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7))
         (=/= ((_.0 z)) ((_.2 z)) ((_.4 z)) ((_.6 z)))
         (sym _.0 _.2 _.4 _.6))))

    (test "not-in-envo-7"
      (run* (q)
        (not-in-envo q '((w . 6) (v . 5))))
      '((_.0
         (=/= ((_.0 v)) ((_.0 w)))
         (sym _.0))))
    
    ))


; should not-in-envo be made a constraint?
(define not-in-envo
  (lambda (x env)
    (fresh ()
      (symbolo x)
      (matche env
        (())
        (((,y . ,v) . ,rest) (symbolo y)
         (=/= y x)
         (not-in-envo x rest))))))

(not-in-envo-tests not-in-envo)


;; CBV lambda calculus, shadowing of lambda handled properly
;; Schemely version
(define eval-exp
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x))
       (lookup x env))
      ((lambda (,x) ,body)
       (guard (symbol? x) (not-in-env 'lambda env))
       `(closure ,x ,body ,env))
      ((,rator ,rand)
       (let ((proc (eval-exp rator env))
             (arg (eval-exp rand env)))
         (pmatch proc
           ((closure ,x ,body ,env2) (guard (symbol? x))
            (eval-exp body `((,x . ,arg) . ,env2)))))))))

(eval-exp-tests eval-exp)

;; Show that this definition of eval-exp doesn't handle shadowing of
;; lambda properly. Test signals an error:
;;
;; pmatch failed
;;  (lambda (x) x)

#|
(test "eval-expo-correct-shadowing-of-lambda"
  (eval-exp
   '((lambda (lambda)
       (lambda (x) x))
     (lambda (w) w))
   '())
  'should-signal-an-error)
|#

;; Closer in spirit to fail-fast mk version,
;; but fixes evaluation order of application
(define eval-exp
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x))
       (lookup x env))
      ((lambda (,x) ,body)
       (guard (symbol? x) (not-in-env 'lambda env))
       `(closure ,x ,body ,env))
      ((,rator ,rand)
       (let ((proc (eval-exp rator env)))
         (pmatch proc
           ((closure ,x ,body ,env2) (guard (symbol? x))
            (let ((arg (eval-exp rand env)))
              (eval-exp body `((,x . ,arg) . ,env2))))))))))

(eval-exp-tests eval-exp)



(define simple-eval-expo-tests
  (lambda (eval-expo)

    (test "simple-eval-expo-1"
      (run* (q) (eval-expo '(lambda (z) z) '() q))
      '((closure z z ())))

    (test "simple-eval-expo-2"
      (run* (q) (eval-expo '((lambda (z) z) (lambda (w) w)) '() q))
      '((closure w w ())))

    (test "simple-eval-expo-3"
      (run* (q)
        (eval-expo
          '((lambda (z)
              ((lambda (z)
                 z)
               (lambda (w) w)))
            (lambda (v) v))
          '()
          q))
      '((closure w w ((z closure v v ())))))

    ;; works even with not-in-envo check
    (test "eval-expo-shadow-lambda-1"
      (run* (q)
        (eval-expo '((lambda (lambda) (lambda lambda)) (lambda (w) w)) '() q))
      '((closure w w ())))

    ;; always works
    (test "eval-expo-shadow-lambda-2a"
      (run* (q)
        (eval-expo
          '((lambda (v)
              (lambda (x) x))
            (lambda (w) w))
          '()
          q))
      '((closure x x ((v closure w w ())))))

    ;; Should return () when using not-in-envo check, since (lambda
    ;; (x) x) is not a legal expression when lambda is bound in the
    ;; environment.  Depends on whether lambda expressions are
    ;; considered built-ins that can't be shadowed.  If so, 'lambda'
    ;; should probably be exclused as a formal argument in a lambda
    ;; expression.
    (test "eval-expo-shadow-lambda-2b"
      (run* (q)
        (eval-expo
          '((lambda (lambda)
              (lambda (x) x))
            (lambda (w) w))
          '()
          q))
      '())
    
    ))

(printf "*** eval-expo 1\n")

;; closely matches Scheme version, but doesn't fail fast
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (proc arg)
         (eval-expo rator env proc)
         (eval-expo rand env arg)
         (matche proc
           ((closure ,x ,body ,env2) (symbolo x)
            (eval-expo body `((,x . ,arg) . ,env2) val))))))))

(simple-eval-expo-tests eval-expo)

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda))) (sym _.0 _.1 _.3))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1)) ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (_.0 _.0))
       (lambda (_.1) (lambda (_.2) _.3)))
      ->
      (closure _.2 _.3
               ((_.1 closure _.1 (lambda (_.2) _.3) ()))))
     (=/= ((_.1 lambda))) (sym _.0 _.1 _.2))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))

(printf "*** eval-expo 2\n")

;; CBV lambda calculus, no shadowing of lambda
;;
;; Closely matches the second Scheme version.  Fixes evaluation order
;; of application.  Can fail faster than the original version, but we
;; can still do better, since we know that the rator must evaluate to
;; a closure.
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (proc)
         (eval-expo rator env proc)
         (matche proc
           ((closure ,x ,body ,env2) (symbolo x)
            (fresh (arg)
              (eval-expo rand env arg)
              (eval-expo body `((,x . ,arg) . ,env2) val)))))))))

(simple-eval-expo-tests eval-expo)

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0)) ((((lambda (_.0) _.0) (lambda (_.1) _.2)) -> (closure _.1 _.2 ())) (sym _.0 _.1)) ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4)) -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ())))) (=/= ((_.0 lambda))) (sym _.0 _.1 _.3)) (((((lambda (_.0) _.0) (lambda (_.1) _.1)) (lambda (_.2) _.3)) -> (closure _.2 _.3 ())) (sym _.0 _.1 _.2)) (((((lambda (_.0) _.0) (lambda (_.1) (lambda (_.2) _.3))) (lambda (_.4) _.5)) -> (closure _.2 _.3 ((_.1 closure _.4 _.5 ())))) (=/= ((_.1 lambda))) (sym _.0 _.1 _.2 _.4))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))


(printf "*** eval-expo 3\n")

;; Replacing the matche within the application clause with explicit
;; unification.
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (x body env2 proc)
         (eval-expo rator env proc)
         (== `(closure ,x ,body ,env2) proc)
         (symbolo x)
         (fresh (arg)
           (eval-expo rand env arg)
           (eval-expo body `((,x . ,arg) . ,env2) val)))))))

(simple-eval-expo-tests eval-expo)



(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda))) (sym _.0 _.1 _.3))
    (((((lambda (_.0) _.0) (lambda (_.1) _.1))
       (lambda (_.2) _.3))
      -> (closure _.2 _.3 ()))
     (sym _.0 _.1 _.2))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1)) ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))



(printf "*** eval-expo 4\n")

;; Lifting introduction of 'arg' variable.
;; Now can arbitrarily reorder goals within application clause.
;; (This is a bit of an overkill, since we really only want to
;; push the 'closure' unification above the rator evaluation )
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (x body env2 proc arg)
         (eval-expo rator env proc)
         (== `(closure ,x ,body ,env2) proc)
         (symbolo x)
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val))))))

(simple-eval-expo-tests eval-expo)



(printf "*** eval-expo 5\n")

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda))) (sym _.0 _.1 _.3))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1)) ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (_.0 _.0))
       (lambda (_.1) (lambda (_.2) _.3)))
      ->
      (closure _.2 _.3
               ((_.1 closure _.1 (lambda (_.2) _.3) ()))))
     (=/= ((_.1 lambda))) (sym _.0 _.1 _.2))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))



(printf "*** eval-expo 6\n")

;; Push up the closure unification to fail fast
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (x body env2 proc arg)
         (== `(closure ,x ,body ,env2) proc)
         (symbolo x)
         (eval-expo rator env proc)
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val))))))

(simple-eval-expo-tests eval-expo)

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda))) (sym _.0 _.1 _.3))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1)) ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (_.0 _.0))
       (lambda (_.1) (lambda (_.2) _.3)))
      ->
      (closure _.2 _.3
               ((_.1 closure _.1 (lambda (_.2) _.3) ()))))
     (=/= ((_.1 lambda))) (sym _.0 _.1 _.2))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))



(printf "*** eval-expo 7\n")

;; Inline proc
;; Final version
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      ((,rator ,rand)
       (fresh (x body env2 arg)
         (symbolo x)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val))))))

(simple-eval-expo-tests eval-expo)

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0)) ((((lambda (_.0) _.0) (lambda (_.1) _.2)) -> (closure _.1 _.2 ())) (sym _.0 _.1)) ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4)) -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ())))) (=/= ((_.0 lambda))) (sym _.0 _.1 _.3)) ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1)) -> (closure _.1 _.1 ())) (sym _.0 _.1)) ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) (lambda (_.2) _.3))) -> (closure _.2 _.3 ((_.1 closure _.1 (lambda (_.2) _.3) ())))) (=/= ((_.1 lambda))) (sym _.0 _.1 _.2))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((lambda (x) (x (lambda (y) x))) (lambda (z) z)) (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))))



(printf "*** eval-expo 8\n")

;; demonstrate reordering for running forward
(define eval-expo
  (lambda (exp env val)
    (matche exp
      ((,rator ,rand)
       (fresh (x body env2 arg)
         (eval-expo body `((,x . ,arg) . ,env2) val)
         (eval-expo rand env arg)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (symbolo x)))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env))
      (,x (symbolo x)
       (lookupo x env val)))))

(test "simple-eval-expo-1"
  (run* (q) (eval-expo '(lambda (z) z) '() q))
  '((closure z z ())))

;; This test diverges
#|
(test "simple-eval-expo-2"
  (run* (q) (eval-expo '((lambda (z) z) (lambda (w) w)) '() q))
  '((closure w w ())))
|#

(test "eval-expo-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0)) ((((lambda (_.0) _.0) (lambda (_.1) _.2)) -> (closure _.1 _.2 ())) (sym _.0 _.1)) ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4)) -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ())))) (=/= ((_.0 lambda))) (sym _.0 _.1 _.3)) (((((lambda (_.0) _.0) (lambda (_.1) _.1)) (lambda (_.2) _.3)) -> (closure _.2 _.3 ())) (sym _.0 _.1 _.2)) (((((lambda (_.0) _.0) (lambda (_.1) (lambda (_.2) _.3))) (lambda (_.4) _.5)) -> (closure _.2 _.3 ((_.1 closure _.4 _.5 ())))) (=/= ((_.1 lambda))) (sym _.0 _.1 _.2 _.4))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z)) ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0)) (((((lambda (_.0) _.0) (lambda (_.1) _.1)) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0 _.1)) (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0)) (((((lambda (_.0) (lambda (_.1) _.1)) (lambda (_.2) _.3)) (lambda (x) (lambda (y) x))) (lambda (z) z)) (=/= ((_.0 lambda))) (sym _.0 _.1 _.2))))
