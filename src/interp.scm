(load "mk.scm")
(load "matche.scm")
(load "pmatch.scm")
(load "test-check.scm")

(define lookup-tests
  (lambda (lookup)

    (test "lookup-1"
      (lookup 'z '((z . 5)))
      5)
    
    ))

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

(define big-omega
  '((lambda (lambda) (lambda lambda))
    (lambda (lambda) (lambda lambda))))

; diverges!
; (eval-exp big-omega '())

(test-check "interp-1"
  (eval-exp
   '(((lambda (x)
        (lambda (y) x))
      (lambda (z) z))
     (lambda (a) a))
   '())
  '(closure z z ()))

(test-check "interp-2"
  (eval-exp
   '((lambda (x)
       (lambda (y) x))
     (lambda (z) z))
   '())
  '(closure y x ((x . (closure z z ())))))

(define fail (== #f #t))

(define lookupo
  (lambda (x env t)
    (conde
      ((== '() env) fail)
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env) (== y x)
         (== v t)))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env) (=/= y x)
         (lookupo x rest t))))))

(test-check "interp-3"
  (run* (q) (lookupo 'y '((x . foo) (y . bar)) q))
  '(bar))

(test-check "interp-4"
  (run* (q) (lookupo 'w '((x . foo) (y . bar)) q))
  '())

(define lookupo
  (lambda (x env t)
    (fresh (y v rest)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))


(test-check "interp-5"
  (run* (q) (lookupo 'y '((x . foo) (y . bar)) q))
  '(bar))

(test-check "interp-6"
  (run* (q) (lookupo 'w '((x . foo) (y . bar)) q))
  '())

(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (rator rand x body env2 a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env2) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (== `(closure ,x ,body ,env) val)
         (not-in-envo 'lambda env)))
      ((symbolo exp) (lookupo exp env val)))))

(test-check "interp-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2))
      ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      ->
      (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda)))
     (sym _.0 _.1 _.3))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1))
      ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (_.0 _.0))
       (lambda (_.1) (lambda (_.2) _.3)))
      ->
      (closure _.2 _.3 ((_.1 closure _.1 (lambda (_.2) _.3) ()))))
     (=/= ((_.1 lambda)))
     (sym _.0 _.1 _.2))))

(test-check "interp-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z))
    ((lambda (x) (x (lambda (y) x))) (lambda (z) z))
    (((lambda (x) (lambda (y) x))
      ((lambda (_.0) _.0) (lambda (z) z)))
     (sym _.0))
    ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x)))
      (lambda (z) z))
     (sym _.0))
    (((lambda (_.0) _.0)
      ((lambda (x) (lambda (y) x)) (lambda (z) z)))
     (sym _.0))))
