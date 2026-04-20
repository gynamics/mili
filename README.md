# MILI

## About
A mini lisp interpreter in 500 lines.

I've always wanted to write a simple but not too crude Lisp implementation in C, but I just didn't have spare time for it. Recently I figured it out in two nights, that's all.

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

## Evaluation
Mili has a mixed lexical/dynamic environment, which is mostly Scheme-style.
- All bindings are stored in environment, which is a list of frames.
  - Each frame is a list of bindings.
  - Each binding is a dotted pairs in form `(SYMBOL . VALUE)`.
- You can access the environment in Lisp, there is a variable `env`, which is a dotted pair,
  - `(car env)` is head of the list, which is used as local environment.
  - `(cdr env)` is tail of the list, which is used as global environment.
- The value of a symbol is always the first value found in DFS order in the environment, otherwise `NIL`.
- The value of `NIL` is `NIL`, this is a built-in type.
- The value of `T` is `T`, this is a lexical binding that can be overriden.
- An address always evaluates to itself.
- Each non-primitive function call use a single frame pushed to the head of current `env` for storing all local bindings.
  When it returns, that frame is poped.

## 15 Primitives
All primitives are lexical bindings that can be overriden.
- `quote`: stop evaluation on its argument, `(quote)` evaluates to `NIL`.
- `eval`: evaluation. (see previous section)
- `apply`: application. (see next section)
- `car`: get object referred by pointer in upper half cell.
- `cdr`: get object referred by pointer in lower half cell.
- `cons`: make a new cell which associates two objects.
- `list`: construct a list, it also accepts `(list a b . c)` to construct a list ended with dotted pair.
- `equal`: test whether two objects are the same.
- `if`: evaluate its first argument, if it is `NIL`, return value of its third argument, otherwise return value of its second argument.
- `atom`: test if its argument is an atom.
- `set`: bind the value of its argument (which must be a symbol) to to the value of its second argument in current lexical scope. It either create new lexical bindings in global environment (tail frame) or modify existing bindings in place.
  - There is a special usage: `(set 'SYMBOL VALUE . SCOPE)` can declare `SCOPE` protected, which restricts its scope. This allows you to lift global environment temporarily.
- `define`: the same as `set`, but it only create new bindings in local environment (head frame) and never override existing bindings.
- `freeze`: get a copy of current environment, compress them in one frame.
  - To save memory, use `(freeze SCOPE)` to make it stops copying at frame `SCOPE`, for example, `(freeze (cdr env))`
- `+` `-` `*` `/` for integer arithmetics, accept one or more arguments, reduce from left to right.

## Application
Note that there is no `lambda` primitive, an applicative expresson should be in form `((TAG PARAMS BODY ...) . ENV)`
- `TAG` should be symbol `f` for function or `m` for macro.
  - If it is a function, its arguments will be evaluated before bound to parameters.
  - A macro is a function that does not evaluate its arguments.
- `PARAMS` is a list of parameters, it can be a list ended with dotted pairs.
- `BODY` is one or more S-expressions to be evaluated.
- `ENV` is the lexical environment (optional), it should be a list of bindings, the same as a env frame.
- For example,
  - `(set 'add2 '((f (x) (+ x 2))))` is a function definition,
  - `(set 'add2 (cons (f (x) (+ x 2)) (freeze (cdr env))))` is a closure definition.
  - `(set 'lambda '((m (name params . body) (cons (list 'f params . body) (freeze (cdr env))))))` is a macro definition..
