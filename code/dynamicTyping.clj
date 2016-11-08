(ns dynamicTyping
  (:require [clojure.string :as Str]
            [clojure.test   :as Test]))

;; =======================================================================================
;; Dynamic Typing
;; =======================================================================================
;; LPFC.
;; We will define the dynamic language from the book here!
;; =======================================================================================
;; Define numbers.

;; The zero element will be the list containing the symbol "zero"
(def zero (list 'zero))
(def zero '(zero))

;; Dynamic values belong to classes we can check which information
;; they are tagged with.
(class zero)

;; Our successor takes a list and cons a "s" symbol to it.
(defn succ [d]
  (cons 's d))

;; Define a few variables.
(def one (succ zero))
(def two (succ (succ zero)))
(def three (succ (succ (succ zero))))
;; =======================================================================================
;; Functions.

;; We can use lisp macros to define fun.
(defmacro fun [d]
  (list 'fn '[x] d))

;; Make identity function and apply it to string "cat".
((fun x) "cat")

;; More functions.
((fun (* 10 x)) 10)
;; =======================================================================================
;; ifz is just a function.

;; If x is zero, return t-Branch,
(defn ifz [x t-branch f-branch]
  (if (= '(zero) x)
    t-branch
    (let [x' (rest x)]
    (f-branch x'))))

(ifz zero one two)

(ifz two one (fn [x] x))
;; =======================================================================================
;; The fix operator.

;; Fix is a little harder to implement...
;; From Harper:
;; _______________________________      (fix)
;;  fix(x.d) |-> [fix(x.d) / x] d

;; =======================================================================================
;; Attempt 1. (Optional)

;; We have x.d, this is an expression, d, abstracted by x. If we want to do
;; [fix(x.d) / x] d, it seems like we should be able to use function application as
;; (d fix(x.d)) since beta reduction will replace all instances of x by fix(x.d) ?
(defn fix-bad [d]
  "fix operator, d must be a function abstracted by x, (fun [x] body)."
    (d (fix-bad d)))

;; (fix-bad (fn [x] x)) ;; Stack overflow!

;; Issue? Clojure is too eager...
;; (fix (fun [x] x))
;; ((fun [x] x) (fix (fun [x] x)))     ; Beta reduction.
;; ((fun [x] x) ((fun [x] x) (fix (fun [x] x))) ; Beta reduction...

;; We don't actually want to evaluate the function. We just want to copy and paste
;; fix(x.d) everywhere we see x...

;; =======================================================================================
;; Attempt 2.

;; Given a list representing function will return the variable this function abstracts over.
(defn fun-var [[name var-vector body]]
  (nth var-vector 0))

;; Given a function will return the body of this function.
(defn fun-body [[name var-vector body]]
  body)

(fun-var '(fn [z] (+ z 1)))
(fun-body '(fn [z] (+ z 1)))

;; Helper function. Implements actual recursion.
(defn subst-h [y d exp]
  (if (list? exp)
    ;; This list might be a function. Skip if same variable is being abstracted.
    (if (and (= (first exp) 'fn) (= y (fun-var exp)))
      exp
      ;; Nope, recurse!
      (map #(subst-h y d %) exp))
    ;; We have a free standing symbol.
    (if (= y exp) d exp)))

;; Given an expression d and a function d of the form, (fn [y] body)
;; it will substitue [y |-> d] body. and return body'.
(defn subst [d exp]
  (let [ y (fun-var exp)
        body (fun-body exp)]
    (subst-h y d body)))

;; Tests...
(subst 1 '(fn [x] (+ x x)))
(subst '(+ 1 2) '(fn [x] (+ x x)))
(subst '(+ 1 2) '(fn [x] (+ x y)))
(subst '(+ 1 2) '(fn [x] (+ x (+ x y))))
(subst '(+ 1 2) '(fn [x] (+ x ((fn [x] x) 3))))

;; _______________________________      (fix)
;;  fix(x.d) |-> [fix(x.d) / x] d

;; Make the fix construct.
;; (fix d) where d the body of a function abstracted by x.
(defn fix [d]
  (let [fix-d (cons 'fix (list d))
        d-var (fun-var d)]
    (subst fix-d d)))

(fix '(fn [x] (+ 1 1)))
(fix '(fn [y'] (succ y')))
;; This is the body of our sum function.
(fix '(fn [p] (fn [y] (ifz y x (fn [y'] (succ (p y')))))))

;; Example:
(def sum (fn [x] (eval (fix '(fn [p] (fn [y] (ifz y x (fn [y'] (succ (p y'))))))))))

;; Here we have a failure. Notice the x in the body of sum is inside the quote ('). So it is not actually evaluated
;; as expected. Furthermore fix returns it's argument unquoted. For subsequent calls to fix it should have returned
;; the code quoted.
(def x three)
((sum x) zero)

;; Example of reduction of sum if it would have worked.
;; ((fn [x] (fix (fn [p] (fn [y] (ifz y x (fn [y'] (succ (p y')))))))) 1 2)  ;; Definition of sum.
;; ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) 2)             ;; Beta reduction.
;; ((fn [y] (ifz y 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y'))))) 2) ;; Step fix.
;; (ifz 2 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y')))) ;; Beta reduction. (argument)
;; (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) 1))      ;; Definition of fix.
;; (succ ((fn [y] (ifz y 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y'))))) 1)) ;; Step fix
;; (succ (ifz 1 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y'))))) ;; Beta reduction (argument)
;; (succ (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) 0))) ;; Definition of fix.
;; (succ (succ (fn [y] (ifz y 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y'))))) 0)) ;; Step fix
;; (succ (succ (ifz 0 1 (fn [y'] (succ ((fix (fn [p] (fn [y] (ifz y 1 (fn [y'] (succ (p y'))))))) y')))))) ;; Beta reduction.
;; (succ (succ 1))  ;; Definition of fix!
;;3                ;; Done!

;; =======================================================================================
;; Some fun with dynamic typing.
;; =======================================================================================

;; Helper function for printf.
(defn replace-list
  "Given a printf formatted string and a list, replace all occurances of
   %* by the elements in the list."
  [f-str [x & xs]]
  (if (nil? x)
    f-str
    (let [f-str' (Str/replace-first f-str #"%." (str x))]
      (replace-list f-str' xs))))

;; Multiple arity function:
(defn printf
  ([s] (print s))
  ([s & x]
   (print (replace-list s x))))


;; The pattern above was just a fold. We can just fold over the function instead.
(defn replace-list'
  [f-str vals]
  (reduce (fn [f-str' val] (Str/replace-first f-str' #"%." (str val)))
          f-str
          vals))

;; Shorthand functions in Clojure.
((fn [x y] (+ x y)) 1 2)
(#(+ %1 %2) 1 2)
(#(+ % %2) 1 2)

(defn replace-list''
  [f-str vals]
  (reduce #(Str/replace-first %1 #"%." (str %2)) f-str vals))


;; Tests.
(replace-list "%d %d %f" '(1 5 10.0))
(replace-list' "%d %d %f" '(1 5 10.0))
(replace-list'' "%d %d %f" '(1 5 10.0))

;; Let's try our variadic function.
(printf "Coordinates| x: %d y : %d" 5 6)
(printf "Hello world!")
(printf "%s %s %s" "one" "two" "three")

;; =======================================================================================
;; Multiple Dispatch
;; =======================================================================================
;; Single Dispatch: at runtime, determine which method to call for an object.

;; See Example.java

;; Multiple dispatch: Clojure Multimethods.
;; Clojure multimethod is a combination of a dispatching function, and one or more methods

;;(defmulti name dispatch-function)

;; defmulti creates new multimethods.

;; defmethod creates and installs a new method of multimethod associated with a dispatch-value.

;; Class is itself a function...
(class class)

;; So we may use the class of a value as the dispatch function to dispatch based on types.
;; Multiple dispatch based on type.
(defmulti class-based-print class)

(class '(1 2 3 4))
(class [1 2 3 4])

(defmethod class-based-print clojure.lang.PersistentList [l]
  (print "It's a list! : l"))

(defmethod class-based-print clojure.lang.PersistentVector [v]
  (print "It's a vector! : v"))

(class-based-print '(1 2 3 4))
(class-based-print [1 2 3 4])


;; Multiple dispatch isn't restricted to types, we can dispatch on arbitrary
;; attributes. Fox example values!
(int 3.0) ; Coerce to int.

(defmulti fib int)

(defmethod fib 0 [_] 1)
(fib 0)

(defmethod fib 1 [_] 1)
(fib 1)

(defmethod fib :default [n]
  (+ (fib (- n 1)) (fib (- n 2))))

(map fib (range 10))



