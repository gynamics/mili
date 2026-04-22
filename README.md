# MILI

## About
A mini lisp interpreter in about 500 lines.

I've always wanted to write a simple Lisp implementation in C, but I just didn't have spare time for it. Recently I figured it out in two nights, that's all.

In this implementation there is only one compound data structure: the list node. So you can almost observe everything in Lisp. However, it is not that friendly to debugging.

## Build
You need a C99 implementation which supports library function `strdup`.

``` shell
gcc -o mili mili.c
```

If you want to see the trace of evaluation/application, add `-DDEBUG` for enabling trace prints.

## Features
- `getline`-based REPL, evaluate line by line, no waiting.
  For each line, only the first sexp is read and evaluated, following things will be neglected.
- Use 5-bit pointer tagging (actually only 3 bits used), 2 bits reserved.
- Use C call stack for recursion, may overflow on very deep recursion.
- Fixed size (8K) stack only for protecting references in GC.
- Fixed size (8K) string table, symbol strings are never freed.
- Fixed size (64K) memory pool with mark-and-sweep GC.
- No strict type check yet, a wrong sentence may cause it crash.

## Syntax
- An `SEXP` is a list or an atom
- An atom is an address or a symbol
- An address is a C numeral that accepted by `stdtoul`, we also use it for unsigned integers (only 57 bits available).
- Otherwise it is a symbol
- `( SEXP* )`for list construction
- `' SEXP` for quote expression construction
- `. SEXP` for dotted pair construction
- ` \v\t\n` for diliminators
- Case sensitive

## Evaluation
Mili has a mixed lexical/dynamic environment, which is mostly Scheme-style.
- All bindings are stored in environment, which is a list of frames.
  - Each frame is a list of bindings.
  - Each binding is a dotted pairs in form `(SYMBOL . VALUE)`.
- You can access the environment in Lisp, there is a variable `env`, which is a dotted pair,
  - `(car env)` is head of a list of frames, this is called local environment.
  - `(cdr env)` is a single frame, which is called called global environment.
- The value of a symbol is always the first value found in the environment, otherwise `nil`.
  The searching order (scoping rule) is firstly searching local environment from head to tail, then search global environment.
- The value of `nil` is `nil`, this is a built-in type.
- The value of `t` is `t`, this is a lexical binding that can be overriden.
- An address always evaluates to itself.
- Each non-primitive function call use a single frame pushed to the head of current `env` for storing all local bindings.
  When it returns, that frame is poped.

## 16 Primitives
All primitives are lexical bindings that can be overriden.
- `quote`: stop evaluation on its argument, `(quote)` evaluates to `nil`.
- `eval`: evaluation. (see previous section)
- `car`: get object referred by pointer in upper half cell.
- `cdr`: get object referred by pointer in lower half cell.
- `cons`: make a new cell which associates two objects.
- `list`: construct a list, it also accepts `(list a b . c)` to construct a list ended with dotted pair.
- `equal`: test whether two objects are the same, return `t` if they're same, otherwise `nil`.
- `if`: evaluate its first argument, if it is `nil`, return value of its third argument, otherwise return value of its second argument.
- `atom`: test if its argument is an atom.
- `set`: bind the value of its first argument (which must be a symbol) to to the value of its second argument in current lexical scope. It either create new lexical bindings in global environment (tail frame) or modify existing bindings in place.
 temporarily.
- `define`: the same as `set`, but it only create new bindings in local environment (head frame) and never override existing bindings. However, `define` may shadow bindings in its parent environments and global environment, because its scope is restricted in local environments.
  - There is a special usage: `(define 'SYMBOL VALUE . MUT)`, if `MUT` is non-nil, it will override existing bindings in local environment.
- `freeze`: get a copy of current environment, compress them in one frame.
  - To save memory, use `(freeze SCOPE)` to make it stops copying at frame `SCOPE`, for example, `(freeze (cdr (car env)))`
- `+` `-` `*` `/` for integer arithmetics, accept one or more arguments, reduce from left to right.

## Application
Note that there is no `lambda` primitive, an applicative expresson should be in form `((TAG PARAMS BODY ...) . ENV)`
- `TAG` should be a symbol which specify type in:
  - `t` for trampoline, a trampoline is a subroutine which is associated with a dirty frame.
  - `f` for function, its arguments will be evaluated before bound to parameters.
  - `m` for macro, a macro is a function that does not evaluate its arguments.
- `PARAMS` is a list of parameters, it can be a list ended with dotted pairs.
- `BODY` is one or more S-expressions to be evaluated.
- `ENV` is the lexical environment (optional), it should be a list of bindings, the same as a env frame.
  - Note that, since `env` is transparent, `ENV` form is not necessarily an independent copy, it can also be a data frame in global environment.
    That also means, a trampoline can modify states in global environment, which can be dangerous.
    Don't abuse `set` of `define` in a trampoline, this structure is designed for implementing tail-recursive subroutines.
- For example,
  - `(set 'count '((t () (define 'x (+ x 1) . t)) ((x . 0))))` is a trampoline definition,
    This define a function `count`, which has a inner counter variable only reachable in this function.
  - `(set 'add2 (list (f (x) (+ x 2))))` is a function definition (with empty capture).
  - `(set 'lambda '((m (params . body) (cons (list 'f params . body) (freeze)))))` is a macro definition.

## Examples

``` lisp
(set 'defmacro '((m (name params . body) (set name (list (list 'm params . body))))))
(defmacro lambda (params . body) (cons (list 'f params . body) (freeze)))
(defmacro defun (name params . body) (set name (eval (list 'lambda params . body))))
(defmacro defsub (name params . body) (set name (list (list 'f params . body))))
(defsub caar (l) (car (car l)))
(defsub cadr (l) (car (cdr l)))
(defsub cdar (l) (cdr (car l)))
(defsub cddr (l) (cdr (cdr l)))
(defsub last (l) (if (cdr l) (last (cdr l)) (car l)))
(defsub mapcar (f l) (if l (cons (f (car l)) (mapcar f (cdr l))) nil))
(defsub reduce (f i l) (if l (reduce f ((eval f) i (car l)) (cdr l)) i))
(mapcar (lambda (x) (+ 1 x)) '(1 2 3 4))
(defmacro call-with-tco (f . args) (define f (list (list 't (car (cdar (eval f))) (cadr (cdar (eval f))))) . t) (define f (cons (car (eval f)) (car env)) . t) (eval (cons f args)))
(call-with-tco mapcar (lambda (x) (+ 1 x)) '(1 2 3 4))
```
