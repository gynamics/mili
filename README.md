# MILI

## About
A mini lisp interpreter in 500 lines.

I've always wanted to write a simple but not too crude Lisp implementation in C, but I just didn't have spare time for it. Recently I figured it out in two nights, that's all.

In this implementation there is only one compound data structure: the list node. So you can almost observe everything in Lisp. However, it is not that friendly to debugging.

## Features
- No strict type check yet, a wrong sentence may cause it crash.
- Use 5-bit pointer tagging (actually only 3 bits used), 2 bits reserved.
- Use C call stack for recursion, may overflow on very deep recursion.
- Syntax:
  - An `SEXP` is a list or an atom
  - An atom is an address or a symbol
  - An address is a C numeral that accepted by `stdtoul`, we also use it for unsigned integers.
  - Otherwise it is a symbol
  - `( SEXP* )`for list construction
  - `' SEXP` for quote expression construction
  - `. SEXP` for dotted pair construction
  - ` \v\t\n` for diliminators
- Mixed lexical/dynamic environment
  - Everything mounted under a reference `env`, which is a list of frames. 
    - Each frame is a list of bindings. 
    - Each binding is a dotted pairs in form `(SYMBOL . VALUE)`.
  - Application creates new frame, dynamic bindings are written to top frame directly, each non-primitive function call use a call frame for storing all local bindings.
- 15 Primitives:
  - `quote`: stop evaluation on its argument
  - `eval`: evaluation
  - `cons`: make a new cell which associates two objects.
  - `list`: construct a list
  - `car`: get object referred by pointer in upper half cell
  - `cdr`: get object referred by pointer in lower half cell 
  - `equal`: test whether two objects are the same
  - `if`: evaluate its first argument, if it is `NIL`, return value of its third argument, otherwise return value of its second argument.
  - `atom`: test if its argument is an atom
  - `set`: bind the value of its argument (which must be a symbol) to to the value of its second argument in current lexical scope. It either create new lexical bindings in the top frame or modify existing bindings in place where it is found.
    - There is a special usage: `(set 'SYMBOL VALUE . SCOPE)` can declare `SCOPE` protected, which restricts its behavior.
  - `define`: the same as `set`, but it only create new lexical bindings (in the top frame) and never override existing bindings.
  - `freeze`: get a copy of current environment
  - `+` `-` `*` `/` for arithmetics
- Note that there is no `lambda` primitive, an applicative expresson should be in form `((TAG PARAMS BODY ...) . ENV)`
  - `TAG` should be symbol `f` for function or `m` for macro.
    - If it is a function, its arguments will be evaluated before bound to parameters.
    - A macro is a function that does not evaluate its arguments.
  - `PARAMS` is a list of parameters, it can be a list ended with dotted pairs.
  - `BODY` is one or more S-expressions to be evaluated.
  - `ENV` is the lexical environment (optional), it should be a list of bindings, the same as a env frame.
  - For example,
    - `(set 'add2 '(f (x) (+ x 2)))` is a function definition,
    - `(set 'add2 (cons (f (x) (+ x 2)) (freeze)))` is a closure definition.
    - `(set 'defun '(m (name params . body) (set 'name (cons (list 'f params body) (freeze)))))` is a macro definition..
- Fixed size (8K) string table, symbol strings are never freed.
- Fixed size (64K) memory pool with mark-and-sweep GC.
- REPL only.

