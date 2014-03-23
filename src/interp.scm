(load "mk.scm")
(load "matche.scm")
(load "pmatch.scm")
(load "test-check.scm")

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

;; can't reorder cond clauses
(define lookup
  (lambda (x env)
    (pmatch env
      (() (error 'lookup "unbound variable"))
      (((,y . ,v) . ,rest)
       (cond
         ((eq? y x) v)
         (else (lookup x rest)))))))

(lookup-tests lookup)

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

(lookup-tests lookup)

;; show lookup still works with  clauses reordered
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

(lookup-tests lookup)



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
    
    ))



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

;; Closer in spriit to fail-fast mk version,
;; but fixes evaluation order of application
(define eval-exp
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x))
       (lookup x env))
      ((lambda (,x) ,body) (guard (symbol? x))
       `(closure ,x ,body ,env))
      ((,rator ,rand)
       (let ((proc (eval-exp rator env)))
         (pmatch proc
           ((closure ,x ,body ,env2) (guard (symbol? x))
            (let ((arg (eval-exp rand env)))
              (eval-exp body `((,x . ,arg) . ,env2))))
           (else (error 'eval-exp "rator does not evaluate to a closure"))))))))

(eval-exp-tests eval-exp)


(define simple-eval-expo-tests
  (lambda (eval-expo)

    (test "simple-eval-expo-1"
      (run* (q) (eval-expo '(lambda (z) z) '() q))
      '((closure z z ())))

    (test "simple-eval-expo-2"
      (run* (q) (eval-expo '((lambda (z) z) (lambda (w) w)) '() q))
      '((closure w w ())))

    ))

;; closely matches Scheme version, but doesn't fail fast
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val))
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
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (sym _.0 _.1 _.3))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0)
         ((lambda (_.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)))
       (lambda (_.6) _.7))
      ->
      (closure _.2 _.3
               ((_.1 closure _.4 _.5 ((_.0 closure _.6 _.7 ())))
                (_.0 closure _.6 _.7 ()))))
     (sym _.0 _.1 _.2 _.4 _.6))
    ((((lambda (_.0) ((lambda (_.1) _.1) (lambda (_.2) _.3)))
       (lambda (_.4) _.5))
      -> (closure _.2 _.3 ((_.0 closure _.4 _.5 ()))))
     (sym _.0 _.1 _.2 _.4))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z))
    (((lambda (x) ((lambda (_.0) _.0) (lambda (y) x)))
      (lambda (z) z))
     (sym _.0))
    (((lambda (_.0) _.0)
      ((lambda (x) (lambda (y) x)) (lambda (z) z)))
     (sym _.0))
    (((lambda (x)
        ((lambda (_.0) ((lambda (_.1) _.0) (lambda (_.2) _.3)))
         (lambda (y) x)))
      (lambda (z) z))
     (=/= ((_.0 _.1))) (sym _.0 _.1 _.2))
    ((lambda (x) (x (lambda (y) x))) (lambda (z) z))))
        

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
       (== `(closure ,x ,body ,env) val))
      ((,rator ,rand)
       (fresh (proc)
         (eval-expo rator env proc)
         (matche proc
           ((closure ,x ,body ,env2) (symbolo x)
            (fresh (arg)
              (eval-expo rand env arg)
              (eval-expo body `((,x . ,arg) . ,env2) val)))))))))

(simple-eval-expo-tests eval-expo)


;; Replacing the matche within the application clause with explicit
;; unification.
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val))
      ((,rator ,rand)
       (fresh (x body env2 proc)
         (eval-expo rator env proc)
         (== `(closure ,x ,body ,env2) proc)
         (symbolo x)
         (fresh (arg)
           (eval-expo rand env arg)
           (eval-expo body `((,x . ,arg) . ,env2) val)))))))

(simple-eval-expo-tests eval-expo)



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
       (== `(closure ,x ,body ,env) val))
      ((,rator ,rand)
       (fresh (x body env2 proc arg)
         (eval-expo rator env proc)
         (== `(closure ,x ,body ,env2) proc)
         (symbolo x)
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val))))))

(simple-eval-expo-tests eval-expo)


;; Push up the closure unification to fail fast
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val))
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
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (sym _.0 _.1 _.3))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0)
         ((lambda (_.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)))
       (lambda (_.6) _.7))
      ->
      (closure _.2 _.3
               ((_.1 closure _.4 _.5 ((_.0 closure _.6 _.7 ())))
                (_.0 closure _.6 _.7 ()))))
     (sym _.0 _.1 _.2 _.4 _.6))
    ((((lambda (_.0) ((lambda (_.1) _.1) (lambda (_.2) _.3)))
       (lambda (_.4) _.5))
      -> (closure _.2 _.3 ((_.0 closure _.4 _.5 ()))))
     (sym _.0 _.1 _.2 _.4))))

(test "eval-expo-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z))
    (((lambda (x) ((lambda (_.0) _.0) (lambda (y) x))) (lambda (z) z))
     (sym _.0))
    (((lambda (_.0) _.0)
      ((lambda (x) (lambda (y) x)) (lambda (z) z)))
     (sym _.0))
    (((lambda (x)
        ((lambda (_.0) ((lambda (_.1) _.0) (lambda (_.2) _.3)))
         (lambda (y) x)))
      (lambda (z) z))
     (=/= ((_.0 _.1))) (sym _.0 _.1 _.2))
    (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z)))
     (sym _.0))))


;; Inline proc
;; Final version
(define eval-expo
  (lambda (exp env val)
    (matche exp
      (,x (symbolo x)
       (lookupo x env val))
      ((lambda (,x) ,body) (symbolo x)
       (== `(closure ,x ,body ,env) val))
      ((,rator ,rand)
       (fresh (x body env2 arg)
         (symbolo x)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val))))))

(simple-eval-expo-tests eval-expo)








(define not-in-env
  (lambda (x env)
    (pmatch env
      (() #t)
      (((,y . ,v) . ,rest) (guard (eq? y x)) #f)      
      (((,y . ,v) . ,rest) (guard (not (eq? y x)))
       (not-in-env x rest)))))

(define eval-exp
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x)) (lookup x env))
      ((,rator ,rand)
       (let ((proc (eval-exp rator env))
             (arg (eval-exp rand env)))
         (pmatch proc
           ((closure ,x ,body ,env2)
            (eval-exp body `((,x . ,arg) . ,env2))))))
      ((lambda (,x) ,body)
       (guard (symbol? x) (not-in-env 'lambda env))
       `(closure ,x ,body ,env)))))

(eval-exp-tests eval-exp)

; diverges!
; (eval-exp big-omega '())




(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))


(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (rator rand x body env2 arg)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (== `(closure ,x ,body ,env) val)
         (not-in-envo 'lambda env)))
      ((symbolo exp) (lookupo exp env val)))))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (rator rand x body env2 proc arg)
         (== `(,rator ,rand) exp)
         (== `(closure ,x ,body ,env2) proc)
         (eval-expo rator env proc)
         (eval-expo rand env arg)
         (eval-expo body `((,x . ,arg) . ,env2) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (== `(closure ,x ,body ,env) val)
         (not-in-envo 'lambda env)))
      ((symbolo exp) (lookupo exp env val)))))

(test "interp-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ()))
     (sym _.0))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4)) -> (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda)))
     (sym _.0 _.1 _.3))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2)) -> (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) ((lambda (_.1) _.1) (lambda (_.2) _.3))) (lambda (_.4) _.5)) -> (closure _.2 _.3 ((_.0 closure _.4 _.5 ()))))
     (=/= ((_.0 lambda)))
     (sym _.0 _.1 _.2 _.4))
    ((((lambda (_.0)
         ((lambda (_.1) (lambda (_.2) _.3))
          (lambda (_.4) _.5)))
       (lambda (_.6) _.7))
      ->
      (closure _.2 _.3 ((_.1 closure _.4 _.5 ((_.0 closure _.6 _.7 ()))) (_.0 closure _.6 _.7 ()))))
     (=/= ((_.0 lambda)) ((_.1 lambda)))
     (sym _.0 _.1 _.2 _.4 _.6))))

(test "interp-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z))
    (((lambda (x) ((lambda (_.0) _.0) (lambda (y) x))) (lambda (z) z))
     (sym _.0))
    (((lambda (_.0) _.0)
      ((lambda (x) (lambda (y) x)) (lambda (z) z)))
     (sym _.0))
    (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z)))
     (sym _.0))
    ((lambda (x) (x (lambda (y) x))) (lambda (z) z))))
