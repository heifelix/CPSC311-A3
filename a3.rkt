#lang plai

; CPSC 311 2016W1 assignment 3: Typed Fun type checker

; BNF of this version of the Fun language:
;
; <Binding> ::= {<symbol> <E>}            ; used in Let*, below
;
;  <E> ::= <num>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {Let <symbol> <E> <E>}
;        | <symbol>
;        | {Lam <symbol> <Type> <E>}
;        | {App <E> <E>}
;
;        | {Rec <symbol> <Type> <E>}
;
;        | {Let* <Binding>... <E>}     -----> syntactic sugar for Let
;                           ^
;                           zero or more
;        | Btrue
;        | Bfalse
;        | {Ite <E> <E> <E>}         ; "if-then-else"
;
;        | {Pair <E> <E>}
;        | {Pair-case <E> {<symbol> <symbol> => <E>}}
;
;        | {Leaf <Type>}             ; leaf node of tree
;        | {Branch <E> <E> <E>}      ; branch node: key, left child, right child
;        | {Tree-case <E> {Leaf => <E>} {Branch <symbol> <symbol> <symbol> => <E>}}
;
;  <Type> ::= num
;           | bool
;           | {* <Type> <Type>}
;           | {-> <Type> <Type>...}
;                              ^ one or more
;           | {tree <Type>}

; Abstract syntax of types
;
(define-type Type
  ; To avoid confusion, the variants of Type begin with a T.
  [Tnum]                                  ; num
  [Tbool]                                 ; bool
  [T*     (t1 Type?)     (t2 Type?)]      ; {* domain range}
  [T->    (domain Type?) (range Type?)]   ; {-> domain range}
  [Ttree  (keys Type?)]                   ; {tree A}
  )

(define-type Typing-context
  [tc/empty]
  [tc/cons-tp    (x symbol?) (A Type?) (rest Typing-context?)]
  )



; Abstract syntax of E (Fun expressions):

(define-type Op
  [Plusop]
  [Minusop]
  [Equalsop]
  [Lessthanop])

; Abstract syntax of E:
(define-type E
  [Num (n number?)]
  [Binop (op Op?) (lhs E?) (rhs E?)]
  [Let (name symbol?) (named-expr E?) (body E?)]
  [Id (name symbol?)]
  
  [Bfalse]
  [Btrue]
  [Ite (scrutinee E?) (then-branch E?) (else-branch E?)]
  
  [Lam (name symbol?) (domain Type?) (body E?)]
  [App (function E?) (argument E?)]
  [Rec (name symbol?) (body-type Type?) (body E?)]
  
  ; pairs
  [Pair (left E?) (right E?)]
  [Pair-case (scrutinee E?) (name1 symbol?) (name2 symbol?) (body E?)]
  
  ; trees
  [Leaf (element Type?)]
  [Branch (key E?) (left E?) (right E?)]
  [Tree-case  (scrutinee E?)
              (leaf-branch E?)
              (key symbol?) (left symbol?) (right symbol?) (branch-branch E?)]
  
  ; Do *not* add variants to this definition! (unless you're doing a bonus problem)
  )

; Parser for Fun expressions
;
(define (parse sexp)
  (cond
    
    [(number? sexp) (Num sexp)]
    
    [(symbol? sexp)
     (case sexp
       [(Bfalse) (Bfalse)]
       [(Btrue)  (Btrue)]
       [else
        (Id sexp)])]
    
    [(list? sexp)
     (let*
         ([head      (first sexp)]
          [args      (rest sexp)]
          [arg-count (length args)])
       
       (case head
         ; {+ sexp1 sexp2}
         ;  ^ ^^^^^^^^^^^ args
         ; head
         [(+) (if (= arg-count 2)
                  (Binop (Plusop) (parse (first args)) (parse (second args)))
                  (error "parse: + needs exactly 2 arguments"))]
         
         [(-) (if (= arg-count 2)
                  (Binop (Minusop) (parse (first args)) (parse (second args)))
                  (error "parse: - needs exactly 2 arguments"))]
         
         [(=) (if (= arg-count 2)
                  (Binop (Equalsop) (parse (first args)) (parse (second args)))
                  (error "parse: = needs exactly 2 arguments"))]
         
         [(<) (if (= arg-count 2)
                  (Binop (Lessthanop) (parse (first args)) (parse (second args)))
                  (error "parse: < needs exactly 2 arguments"))]
         
         [(Let*) (case arg-count
                   [(0)  (error "parse: Let* with no body")]
                   [(1)  (parse (first args))]
                   [else ; arg-count >= 2
                    (let ([binding1-sexp (first args)])
                      (if (list? binding1-sexp)
                          (let ([x1-sexp (first binding1-sexp)]
                                [e1-sexp (second binding1-sexp)])
                            (if (symbol? x1-sexp)
                                (Let x1-sexp
                                     (parse e1-sexp)
                                     (parse (cons 'Let* (rest args))))
                                (error "parse: Let* needs a symbol")))
                          (error "parse: each Let* binding must be bracketed")))]
                   )]
         
         [(Ite) (if (= arg-count 3)
                    (Ite (parse (first args))
                         (parse (second args)) 
                         (parse (third args)))
                    (error "parse needs exactly 3 arguments"))]
         
         [(Lam) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (Lam (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: lam must be followed by an identifier"))
                    (error "parse: malformed `lam'"))]
         
         [(App) (if (= arg-count 2)
                    (App (parse (first args)) (parse (second args)))
                    (error "parse: app needs 1 function and 1 argument"))]
         
         [(Rec) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (Rec (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: rec must be followed by an identifier"))
                    (error "parse: malformed `rec'"))]
         
         [(Let) (if (= arg-count 3)
                    (let ([name (first args)]
                          [named-sexp (second args)]
                          [body-sexp  (third args)])
                      (if (symbol? name)
                          (Let name (parse named-sexp) (parse body-sexp))
                          (error "parse: malformed `Let'")))
                    (error "parse: malformed `Let'"))]
         
         [(Pair) (if (= arg-count 2)
                     (Pair (parse (first args))
                           (parse (second args)))
                     (error "parse: malformed `pair'"))]
         
         [(Pair-case) (parse-pair-case arg-count args)]
         
         [(Leaf)     (if (= arg-count 1)
                         (Leaf (parse-type (first args)))
                         (error "parse: malformed `Leaf'"))]
         
         [(Branch)   (if (= arg-count 3)
                         (Branch (parse (first args)) (parse (second args)) (parse (third args)))
                         (error "parse: malformed `Branch'"))]
         
         [(Tree-case) (parse-tree-case arg-count args)]
         
         [else (error "parse: syntax error")]))]
    
    [else (error "parse: syntax error")]))

; parse-pair-case : sexp -> E
;
(define (parse-pair-case arg-count args)
  (if (= arg-count 2)
      
      (let ([scrutinee (parse (first args))]
            [inner-sexp (second args)])
        
        (if (and (list? inner-sexp)
                 (= (length inner-sexp) 4)
                 (symbol? (first inner-sexp))
                 (symbol? (second inner-sexp))
                 (symbol=? (third inner-sexp) '=>))
            
            (let ([name1 (first inner-sexp)]
                  [name2 (second inner-sexp)]
                  [body (parse (fourth inner-sexp))])
              
              (Pair-case scrutinee name1 name2 body))
            
            (error "parse: malformed `pair-case'")))
      
      (error "parse: malformed `pair-case'")))

; parse-tree-case
;
(define (parse-tree-case arg-count args)
  (if (= arg-count 3)
      
      (let ([scrutinee (parse (first args))]
            [leaf-branch-sexp (second args)]
            [branch-branch-sexp (third args)]
            )
        
        (if (and (list? leaf-branch-sexp)
                 (= (length leaf-branch-sexp) 3)
                 (symbol=? (first leaf-branch-sexp) 'Leaf)
                 (symbol=? (second leaf-branch-sexp) '=>))
            
            (let ([leaf-branch (parse (third leaf-branch-sexp))])
              
              (if (and (list? branch-branch-sexp)
                       (= (length branch-branch-sexp) 6)
                       (symbol=? (first branch-branch-sexp) 'Branch)
                       (symbol? (second branch-branch-sexp))
                       (symbol? (third branch-branch-sexp))
                       (symbol? (fourth branch-branch-sexp))
                       (symbol=? (fifth branch-branch-sexp) '=>))
                  
                  (let ([xKey (second branch-branch-sexp)]
                        [xL (third branch-branch-sexp)]
                        [xR (fourth branch-branch-sexp)]
                        [branch-branch (parse (sixth branch-branch-sexp))])
                    
                    (Tree-case scrutinee leaf-branch xKey xL xR branch-branch))
                  (error "parse: malformed `Tree-case'")))
            (error "parse: malformed `Tree-case'")))
      (error "parse: malformed `Tree-case'")))


; build-> : listof Type -> Type
;
; Given (list A1 ... A(n-1) An), returns
;
;    (T-> A1 (T-> A2 ... (T-> A(n-1) An)))
;
; Precondition: n >= 2
;
(define (build-> types)
  (if (= (length types) 2)
      (T-> (first types) (second types))
      (T-> (first types) (build-> (rest types)))))

; parse-type : sexp -> Type
;
(define (parse-type sexp)
  (cond
    [(symbol? sexp)
     (case sexp
       [(num)    (Tnum)]
       [(bool)   (Tbool)]
       [(tree)   (error "tree must be written {tree <Type>}")]
       [(Num)    (error "num (as a type) must not be capitalized")]
       [(Bool)   (error "bool must not be capitalized")]
       [else     (error "unknown type name")]
       )]
    [(list? sexp)
     (if (empty? sexp)
         (error "parse-type: empty")
         (let*
             ([head      (first sexp)]
              [args      (rest sexp)]
              [arg-count (length args)])
           
           (case head
             [(*)    (T* (parse-type (first args)) (parse-type (second args)))]
             [(->)   (build-> (map parse-type args))]
             [(tree) (Ttree (parse-type (first args)))]
             [(Tree) (error "tree must not be capitalized")]
             [else   (error "unknown type constructor " head)])))]
    [else (error "unknown animal in type")]))


; subst : E symbol E -> E
;
; (subst e2 x e1) returns e1 with x replaced by e2.
;
(define (subst e2 x e1)
  (type-case E e1
    [Num (n) (Num n)]
    
    [Bfalse () (Bfalse)]
    
    [Btrue () (Btrue)]
    
    [Binop (op eL eR) (Binop op (subst e2 x eL) (subst e2 x eR))]
    
    [Let (y e eB)
         (if (symbol=? x y)
             (Let x (subst e2 x e) eB) 
             (Let y (subst e2 x e) (subst e2 x eB)))]
    
    [Lam (y A eB)
         (if (symbol=? x y)
             ; same symbol; if x appears inside eB, it refers to *this*
             ;  binding, not to the x we're replacing, so return same eB
             (Lam x A eB)      
             
             ; different symbol; leave y alone and replace inside eB
             (Lam y A (subst e2 x eB))             
             )]
    
    [App (eFun eArg) (App (subst e2 x eFun) (subst e2 x eArg))]
    
    [Rec (y A eB)     ; Rec binds y, so treat it the same way as Lam
         (if (symbol=? x y)
             (Rec x A eB)
             (Rec y A (subst e2 x eB)))]
    
    [Ite (e left right)   (Ite (subst e2 x e) (subst e2 x left) (subst e2 x right))]
    
    [Id (y)
        (if (symbol=? x y)
            e2
            (Id y))]
    
    [Pair (left right)   (Pair (subst e2 x left) (subst e2 x right))]
    [Pair-case (scrutinee name1 name2 body)
               
               (Pair-case (subst e2 x scrutinee) name1 name2 
                          (if (or (symbol=? x name1) (symbol=? x name2))
                              body
                              (subst e2 x body)))]
    
    [Leaf (A) (Leaf A)]
    [Branch (ek eL eR) (Branch (subst e2 x ek) (subst e2 x eL) (subst e2 x eR))]
    
    [Tree-case (e eEmpty xkey xleft xright eBranch)
               (Tree-case (subst e2 x e)
                          (subst e2 x eEmpty)
                          xkey
                          xleft
                          xright
                          (if (or (symbol=? x xkey)
                                  (symbol=? x xleft)
                                  (symbol=? x xright))
                              eBranch
                              (subst e2 x eBranch)))]
    ))


; racket-boolean-to-Fun-boolean : bool? -> E?
;
; Postcondition: result is Bfalse or Btrue

(define (racket-boolean-to-Fun-boolean b)
  (if b
      (Btrue)
      (Bfalse)))



; valid-binop : Op? E? E? -> boolean?
;
; valid-binop op v1 v2 returns true iff v1 and v2 are consistent with op:
;    If op is plusop or minusop, then v1 and v2 must be nums.
;    If op is equalsop or lessthanop, then v1 and v2 must be nums.
;
; Precondition: v1 and v2 are values (i.e., num, lam, Bfalse, or Btrue).

(define (valid-binop op v1 v2)
  (type-case Op op
    [Plusop ()      (and (Num? v1) (Num? v2))]
    [Minusop ()     (and (Num? v1) (Num? v2))]
    [Equalsop ()    (and (Num? v1) (Num? v2))]
    [Lessthanop ()  (and (Num? v1) (Num? v2))]
    
    ; This code is redundant, but it makes it easy to match an operator with
    ; its valid arguments, and is easier to extend if we add operators whose
    ; arguments aren't numbers.
    ))


; apply-binop : Op? E? E? -> E?
;
; apply-binop op v1 v2 applies op to v1 and v2, returning an expression.
; Used in interp, below.
;
; Precondition:
;    1.  v1 and v2 are values (i.e., num, lam, Bfalse, or Btrue).
;    2.  (valid-binop op v1 v2)

; Postcondition:
;    If op is plusop or minusop, result is a num.
;    If op is equalsop or lessthanop, result is Bfalse or Btrue.

(define (apply-binop op v1 v2)
  (type-case Op op
    [Plusop ()      (Num (+ (Num-n v1) (Num-n v2)))]
    [Minusop ()     (Num (- (Num-n v1) (Num-n v2)))]
    [Equalsop ()    (racket-boolean-to-Fun-boolean (= (Num-n v1) (Num-n v2)))]
    [Lessthanop ()  (racket-boolean-to-Fun-boolean (< (Num-n v1) (Num-n v2)))]))


; Interpreter for Fun expressions:
;
; interp : E? -> E?
;
; Given an E e, return the E v such that
;
;                e ⇓ v
;
; according to the rules specified in Assignment 2.

(define (interp e)
  (type-case E e
    
    ; Values evaluate to themselves:
    [Num (n)       (Num n)]
    [Lam (x A eB)  (Lam x A eB)]
    [Bfalse ()     (Bfalse)]
    [Btrue ()      (Btrue)]
    [Leaf (A)      (Leaf A)]
    
    ; Non-values:
    [App (e1 e2)
         (let ([v1 (interp e1)])
           (type-case E v1
             [Lam (x A eB)
                  (let* ([v2 (interp e2)]
                         [v (interp (subst v2 x eB))])
                    v)]
             [else (error "tried to apply non-lam")]
             ))]
    
    [Rec (u B eB)
         (let ([v (interp (subst (Rec u B eB) u eB))])
           v)]
    
    [Binop (op e1 e2)
           (let* ([v1 (interp e1)]
                  [v2 (interp e2)])
             (if (valid-binop op v1 v2)
                 (let ([v  (apply-binop op v1 v2)])
                   v)
                 (error "binop applied to invalid arguments")))]
    
    [Let (x e1 e2)
         (let* ([v1 (interp e1)]
                [v2 (interp (subst v1 x e2))])
           v2)]
    
    [Id (x)
        (error "free-variable")]
    
    [Ite (eCond eThen eElse)
         (let ([vCond (interp eCond)])
           (type-case E vCond
             [Btrue ()   (interp eThen)]
             [Bfalse ()  (interp eElse)]
             [else (error "Ite on a non-boolean")]))]
    
    [Pair (e1 e2)
          (let ([v1  (interp e1)]
                [v2  (interp e2)])
            (Pair v1 v2))]
    
    [Pair-case (ePair x1 x2 eB)
               (let ([vPair  (interp ePair)])
                 (type-case E vPair
                   [Pair (v1 v2)  (interp (subst v2 x2 (subst v1 x1 eB)))]
                   [else (error "pair-case on a non-pair")]))]
    
    [Branch (eKey eL eR)
            (let ([vKey (interp eKey)]
                  [vL (interp eL)]
                  [vR (interp eR)])
              (Branch vKey vL vR))]
    
    [Tree-case (eTree eLeaf xKey xL xR eBranch)
               (let ([vTree  (interp eTree)])
                 (type-case E vTree
                   [Leaf (A)             (interp eLeaf)]
                   [Branch (vKey vL vR)  (interp (subst vR xR
                                                        (subst vL xL
                                                               (subst vKey xKey eBranch))))]
                   [else (error "tree-case on a non-tree")]))]
    ))


(define (unparse-op op)
  (type-case Op op
    [Plusop ()      `+]
    [Minusop ()     `-]
    [Equalsop ()    `=]
    [Lessthanop ()  `<]))

; unparse-type : (or false Type) -> (or false sexp)
;
; Given abstract syntax type A, return its concrete syntax (s-expression).
; Or, if given #false, return #false.
(define (unparse-type A)
  (if A
      (type-case Type A
        [Tnum ()             `num]
        [Tbool ()            `bool]
        [T-> (domain range)  `(-> ,(unparse-type domain) ,(unparse-type range))]
        [T*  (A1 A2)         `(*  ,(unparse-type A1) ,(unparse-type A2))]
        [Ttree (A)           `(tree ,(unparse-type A))]
        )
      #false))

(define (unparse e)
  (type-case E e
    [Num (n)                   n]
    [Binop (op e1 e2)          `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
    [Id (x)                    x]
    [Let (x e1 eB)             `(Let ,x ,(unparse e1) ,(unparse eB))] 
    [Lam (x A body)            `(Lam ,x ,(unparse-type A) ,(unparse body))]
    [App (e1 e2)               `(App ,(unparse e1) ,(unparse e2))]
    [Rec (u B body)            `(Rec ,u ,(unparse-type B) ,(unparse body))]
    [Bfalse ()                 `Bfalse]
    [Btrue ()                  `Btrue]
    [Ite (e e1 e2)             `(Ite ,(unparse e) ,(unparse e1) ,(unparse e2))]
    
    [Pair (e1 e2)              `(Pair ,(unparse e1) ,(unparse e2))]
    [Pair-case (e x1 x2 body)  `(Pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]
    
    [Leaf (A)                  `(Leaf ,(unparse-type A))]
    [Branch (eKey eL eR)       `(Branch ,(unparse eKey) ,(unparse eL) ,(unparse eR))]
    [Tree-case (e eLeaf xk xl xr eBranch)
               `(Tree-case ,(unparse e)
                           (Leaf               => ,(unparse eLeaf))
                           (Branch ,xk ,xl ,xr => ,(unparse eBranch)))]
    ))


(define (do-parse input)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (printf "          input: ~v\n" input)
    (printf "abstract syntax: ~v\n" abstract-exp)
    (printf "unparsed syntax: ~v\n" concrete-exp)
    ))

(define (do-parse-interp input)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (printf "          input: ~v\n" input)
    (printf "abstract syntax: ~v\n" abstract-exp)
    (printf "unparsed syntax: ~v\n\n" concrete-exp)
    (let ([v (interp abstract-exp)])
      (printf "\nresult of evaluation: ~v\n" v)
      (printf "     unparsed result: ~v\n\n" (unparse v)))))



; look-up-type : Typing-context symbol -> Type
;
(define (look-up-type context x)
  (type-case Typing-context context
    [tc/empty ()  (error "look-up-type: not in scope: " x)]
    [tc/cons-tp (y A context)       (if (symbol=? x y)
                                        A
                                        (look-up-type context x))]
    ))

; type=? : Type Type -> boolean
;
; Check that two types are equal.
(define (type=? A B)
  (and A         ; weed out stray #false results
       B     
       (type-case Type A
         ; [Tnum ()  handled by else branch]
         ; [Tbool () handled by else branch]
         [T* (A1 A2)   (type-case Type B [T* (B1 B2)   (and (type=? A1 B1)
                                                            (type=? A2 B2))]
                         [else #f])]
         
         [T-> (A1 A2)  (type-case Type B [T-> (B1 B2)  (and (type=? B1 A1)
                                                            (type=? A2 B2))]
                         [else #f])]
         [Ttree (A0)   (type-case Type B
                         [Ttree (B0)     (type=? A0 B0)]
                         [else #f])]
         [else    
          (equal? A B)])))

; op-signature : Op -> Type
;
(define (op-signature op)
  (let* ([num*num        (T* (Tnum) (Tnum))]
         [num*num->num   (T-> num*num (Tnum))]
         [num*num->bool  (T-> num*num (Tbool))])
    (type-case Op op
      [Plusop ()     num*num->num]
      [Minusop ()    num*num->num]
      [Lessthanop () num*num->bool]
      [Equalsop ()   num*num->bool]
      )))

;
; typeof : Typing-context E -> (or false Type)
;
(define (typeof tc e)
  (type-case E e
    
    [Num (n)               (Tnum)]
    
    [Binop (op e1 e2)      (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (and A1
                                  A2
                                  (type-case Type (op-signature op)
                                    [T-> (domain range)
                                         (if (type=? domain (T* A1 A2))
                                             range
                                             #false)]
                                    [else (error "strange op signature: " op " : " (op-signature op))])))]
    
    [Bfalse ()             (Tbool)]
    [Btrue ()              (Tbool)]
    
    [Ite (e eThen eElse)   (and (Tbool? (typeof tc e))
                                (let ([AThen (typeof tc eThen)]
                                      [AElse (typeof tc eElse)])
                                  (and (type=? AThen AElse)
                                       AThen)))]
    
    [Id (x)                (let ([A (look-up-type tc x)])
                             (or A
                                 (begin
                                   (printf "unbound identifier ~v~n" x)
                                   #false)))]
    
    [Let (x e eBody)      (let ([A (typeof tc e)])
                            (and A
                                 (let* ([tc-extended  (tc/cons-tp x A tc)]
                                        [B            (typeof tc-extended eBody)])
                                   B)))]
    
    [Lam (x A eBody)       (let* ([tc-extended  (tc/cons-tp x A tc)]
                                  [B (typeof tc-extended eBody)])
                             (and B
                                  (T-> A B)))]
    
    [Rec (u B eBody)       (let* ([tc-extended  (tc/cons-tp u B tc)]
                                  [B2 (typeof tc-extended eBody)])
                             (and (type=? B B2)
                                  B))]
    
    [App (eFun eArg)       (let* ([AFun (typeof tc eFun)]
                                  [AArg (typeof tc eArg)])
                             (and AFun
                                  (type-case Type AFun
                                    [T-> (A1 A2)  (if (type=? A1 AArg)
                                                      A2
                                                      #false)]
                                    [else          #false])))]
    
    [Pair (e1 e2)          (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (and A1
                                  A2
                                  (T* A1 A2)))]
    
    [Pair-case (e x1 x2 eBody)
               (let* ([scrutinee (typeof tc e)])(type-case Type scrutinee
                        [T* (A1 A2) (let* ([tc-extended (tc/cons-tp x1 A1 tc)]
                                           [tc-extended (tc/cons-tp x2 A2 tc-extended)]
                                           [B (typeof tc-extended eBody)])
                                      (and A1
                                           A2
                                           B))]
                        [else #false]))]
    
    [Leaf (A)               (error "unimplemented")]
    [Branch (eKey eL eR)    (error "unimplemented")]
    
    [Tree-case (e eLeaf xKey xL xR eBranch)     
               (error "unimplemented")
               ]
    
    ))

(define (typeof-program e)
  (typeof (tc/empty) e))

(typeof-program (parse '{Ite Bfalse {Let x Btrue x} {Let y Bfalse y}}))
(interp         (parse '{Ite Bfalse {Let x Btrue x} {Let y Bfalse y}}))

; (typeof-program (parse '{Ite Bfalse {Let x Btrue x} y}))   ; y not in scope
; (interp         (parse '{Ite Bfalse {Let x Btrue x} y}))

; (typeof-program (parse '{Ite Btrue {Let x Btrue x} y}))  ; y not in scope
(interp         (parse '{Ite Btrue {Let x Btrue x} y}))

(typeof-program (parse '{Ite Bfalse {Let x Btrue x} {Let y 3 y}}))
(interp         (parse '{Ite Bfalse {Let x Btrue x} {Let y 3 y}}))


(typeof-program
 (parse '{Let*
          {multiply {Rec m
                         {-> num num num}
                         {Lam x num {Lam y num {Ite {= y 0}
                                                    0
                                                    {Ite {= y 1}
                                                         x
                                                         {+ x {App {App m x} {- y 1}}}}}}}}}
          {fact {Rec u {-> num num} {Lam n num {Ite {< n 2}
                                                    1
                                                    {Let c {App u {- n 1}}
                                                         {App {App multiply n} c}}}}}}
          {App fact 5}}))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Problem 3
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; In each part, if you find a Fun expression that matches the problem
; specification, write it (as abstract syntax, or call parse on concrete syntax)
; in place of #false.
;
; If you do not think such an expression exists, leave #false in place
; and write a comment to *briefly* explain why you think there is no
; such expression.
;
; You can use pairs and lists in these expressions **ONLY** if you have
; completed those problems.  So you can't use the (error "unimplemented")
; branches we left in `typeof' to claim that an expression doesn't typecheck.

; Part 3a (evaluates; rejected by typeof)
(define (expr-3a)
  (typeof-program (parse '{Pair-case 1 {x1 x2 => {= 3 x2}}}))
  )

; Part 3b (does not evaluate; accepted by typeof)
(define expr-3b
  #false
  )

; Part 3c (evaluates to a lam, has type {-> bool bool},
;          and evaluates to a value iff its argument is Bfalse)
(define expr-3c
  #false
  )

; Part 3d (has type {-> {-> bool bool} bool}
;          and, when applied to any function f of type {-> bool bool},
;          evaluates to a value iff {App f Bfalse} evaluates to a value)
(define expr-3d
  #false
  )

; Part 3e: same as 3d, but evaluates to a value
;                      iff {App f Bfalse} does *not* evaluate to a value
(define expr-3e
  #false
  )

; Tests to check that you either have #false, or an expression
; (not necessarily well-typed!).
;
; If any of these 5 tests fail, you will receive 0 marks for Problem 3.
(test (or (not expr-3a) (E? expr-3a)) #true)
(test (or (not expr-3b) (E? expr-3b)) #true)
(test (or (not expr-3c) (E? expr-3c)) #true)
(test (or (not expr-3d) (E? expr-3d)) #true)
(test (or (not expr-3e) (E? expr-3e)) #true)








(test (typeof-program (parse '{Pair 2 Btrue})) (parse-type '{* num bool}))
(test (typeof-program (parse '{Pair 2 3})) (parse-type '{* num num}))

(test (typeof-program (parse '{Lam x num x})) (parse-type '{-> num num}))
(test (typeof-program (parse '{Lam x bool x})) (parse-type '{-> bool bool}))

(test (typeof-program (parse '{Leaf num})) (parse-type '{tree num}))
(test (typeof-program (parse '{Branch 1 {Leaf bool} {Leaf bool}})) #false)
(test (typeof-program (parse '{Tree-case {Branch 1 {Leaf num} {Leaf num}} {Leaf => 0} {Branch k l r => k}})) (parse-type 'num))

(test (unparse (interp (parse '{Tree-case {Leaf num} {Leaf => 0} {Branch k l r => l}}))) 0)


; Our Own Tests
(test (typeof-program (parse '{Pair Btrue Bfalse})) (parse-type '{* bool bool}))
(test (typeof-program (parse '{Pair Bfalse 3})) (parse-type '{* bool num}))
(test (typeof-program (parse '{Pair 111 3})) (parse-type '{* num num}))
(test (typeof-program (parse '{Pair-case {Pair 1 3} {x1 x2 => {- 3 x2}}})) (Tnum))
(test (typeof-program (parse '{Pair-case {Pair 1 3} {x1 x2 => {= 3 x2}}})) (Tbool))
(test (typeof-program (parse '{Pair-case 1 {x1 x2 => {= 3 x2}}})) #f)