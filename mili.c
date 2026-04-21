/** mili.c: MIni LIsp in C
 *
 * A Scheme-style Lisp implementation in about 500 lines.
 *
 * CopyRevolted 2026 by gynamics
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uintptr_t Ref;

#define TAG_BITS 5
#define TAGPTR_BITS (64 - TAG_BITS)
#define TAG_MASK (~0UL << TAGPTR_BITS)
#define TAGPTR_MASK (~TAG_MASK)
#define TAGTYPE_BITS 3
#define TAGTYPE_MASK (TAG_MASK ^ (TAG_MASK << TAGTYPE_BITS))

typedef enum {
  REF_NIL,
  REF_LIST,
  REF_SYMBOL,
  REF_ADDR,
  REF_ERROR,
} RefType;

static inline Ref makeRef(Ref p, RefType type) {
  return (Ref)((p & TAGPTR_MASK) | ((uintptr_t)type << TAGPTR_BITS));
}

static inline void *unRef(Ref ref) { return (void *)(ref & TAGPTR_MASK); }

typedef enum {
  ERR_EVAL,
  ERR_TYPE,
} ErrType;

static inline Ref errRef(ErrType err) {
  printf("Error %d\n", err);
  return (Ref)(((uintptr_t)REF_ERROR << TAGPTR_BITS) | (uintptr_t)err);
}

static inline RefType getRefType(Ref ref) {
  return (RefType)((ref & TAGTYPE_MASK) >> (TAGPTR_BITS));
}

static inline int testRefType(Ref ref, RefType type) {
  return (getRefType(ref) == type);
}
#define NIL_P(ref) testRefType(ref, REF_NIL)
#define LIST_P(ref) testRefType(ref, REF_LIST)

typedef struct {
  Ref car;
  Ref cdr;
} Node, *List;

#define NIL ((Ref)((uintptr_t)REF_NIL << TAGPTR_BITS))
#define T ((Ref)((uintptr_t)SYM_t | ((uintptr_t)REF_SYMBOL << TAGPTR_BITS)))
#define LIST(ref) ((List)unRef(ref))
#define CAR(ref) (LIST(ref)->car)
#define CDR(ref) (LIST(ref)->cdr)
#define UINT(ref) ((unsigned long)unRef(ref))

Ref miliCar(Ref x) {
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CAR(x);
  default:
    return errRef(ERR_TYPE);
  }
}

Ref miliCdr(Ref x) {
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CDR(x);
  default:
    return errRef(ERR_TYPE);
  }
}

#define HEAP_SIZE 4096
static Node heap[HEAP_SIZE];
static int freelist[HEAP_SIZE];
static int fltop;
static uint8_t marked[HEAP_SIZE];
static inline size_t heapPos(Ref x) { return LIST(x) - heap; }
void mark(Ref x) {
  if (LIST_P(x)) {
    size_t pos = heapPos(x);
    if (!marked[pos]) {
      marked[pos] += 1;
      mark(CAR(x));
      mark(CDR(x));
    }
  }
}

void sweep() {
  for (int i = 0; i < HEAP_SIZE; i++)
    if (!marked[i])
      freelist[fltop++] = i;
    else
      marked[i] -= 1;
}

#define ENV ((Ref)heap | ((uintptr_t)REF_LIST << TAGPTR_BITS))
Ref miliCons(Ref car, Ref cdr) {
  if (fltop == 0) { // trigger GC only if no more free nodes
#ifdef DEBUG
    printf("\nGC triggered.\n\n");
#endif
    mark(ENV);
    sweep();
#ifdef DEBUG
    printf("\nGC: %d nodes collected.\n\n", fltop);
#endif
    if (fltop == 0)
      fprintf(stderr, "Oops, heap is fully occupied!\n");
  }
  List x = &heap[freelist[--fltop]];
  x->car = car;
  x->cdr = cdr;
  return makeRef((Ref)x, REF_LIST);
}

typedef enum {
  SYM_quote,
  SYM_t,
  SYM_m,
  SYM_f,
  SYM_env,
  SYMCNT,
} PreDefinedSymbols;

static char *symtbl[1024];
static int symcnt;
char *miliSymbolName(Ref id) { return symtbl[UINT(id)]; }
Ref miliIntern(char *s) {
  for (int i = 0; i < symcnt; ++i)
    if (strcmp(s, symtbl[i]) == 0)
      return makeRef((Ref)i, REF_SYMBOL);
  /* not found, insert it */
  symtbl[symcnt++] = strdup(s);
  return makeRef((Ref)(symcnt - 1), REF_SYMBOL);
}

Ref miliApply(Ref fexp, Ref args);
Ref miliPrint(Ref exp);
Ref miliGetLocal(Ref key) {
  Ref p, q;
  for (p = CAR(ENV); p != miliCdr(CAR(ENV)); p = CDR(p))
    for (q = CAR(p); LIST_P(q); q = CDR(q))
      if (key == CAR(CAR(q)))
        return CAR(q);
  return NIL;
}

Ref miliGet(Ref key) {
  Ref p, q;
  p =  miliGetLocal(key);
  if (p == NIL) {
    for (q = CDR(ENV); LIST_P(q); q = CDR(q))
      if (key == CAR(CAR(q)))
        return CAR(q);
    return NIL;
  } else return p;
}

Ref miliEval(Ref exp) {
#ifdef DEBUG
  static int d = 0;
  printf("Eval{%d} ", d++), miliPrint(exp);
  printf(" :: type%d\n", getRefType(exp));
#endif
  Ref ret;
  switch (getRefType(exp)) {
  case REF_NIL:
    ret = NIL;
    break;
  case REF_LIST:
    if (NIL_P(CAR(exp)))
      ret = NIL; // () => nil
    else
      ret = miliApply(CAR(exp), CDR(exp));
    break;
  case REF_SYMBOL:
    ret = miliCdr(miliGet(exp));
    break;
  case REF_ADDR:
    ret = exp;
    break;
  default:
    ret = errRef(ERR_EVAL);
  }
#ifdef DEBUG
  printf("{%d} => ", --d), miliPrint(ret), printf("\n");
#endif
  return ret;
}

Ref miliSet(Ref key, Ref value) {
  if (!testRefType(key, REF_SYMBOL))
    return errRef(ERR_TYPE);
  Ref cell = miliGetLocal(key);
  if (NIL_P(cell))
    CDR(ENV) = miliCons(miliCons(key, value), CDR(ENV));
  else
    CDR(cell) = value;
  return value;
}

Ref miliDefine(Ref key, Ref value, Ref mut) {
  if (!testRefType(key, REF_SYMBOL))
    return errRef(ERR_TYPE);
  Ref cell = miliGetLocal(key);
  if (NIL_P(cell)) {
    CAR(CAR(ENV)) = miliCons(miliCons(key, value), CAR(CAR(ENV)));
    return value;
  } else if (NIL_P(mut))
    return CDR(cell);
  else
    return (CDR(cell) = value);
}

Ref miliFreeze(Ref scope) {
  Node n = {NIL, NIL};
  Ref r = makeRef((Ref)&n, REF_LIST);
  for (Ref p = CAR(ENV); p != scope; p = CDR(p))
    for (Ref q = CAR(p); LIST_P(q); q = CDR(q)) {
      Ref b = CAR(q);
      // duplicate bindings are not removed but left behind
      CDR(r) = miliCons(miliCons(CAR(b), CDR(b)), NIL);
      r = CDR(r);
    }
  return n.cdr;
}

Ref miliApply(Ref fexp, Ref args) {
#ifdef DEBUG
  printf("Apply "), miliPrint(fexp), printf(" "), miliPrint(args), printf("\n");
#endif
  Ref f = miliEval(fexp);
  switch (getRefType(f)) {
  case REF_ADDR:
    return ((Ref (*)(Ref))unRef(f))(args);
  case REF_LIST: {
    if (!LIST_P(f) || !LIST_P(CAR(f)) || !testRefType(CAR(CAR(f)), REF_SYMBOL))
      return errRef(ERR_TYPE);
    int ftype = UINT(CAR(CAR(f)));
    int macrop = (ftype == SYM_m);
    Ref p, q, r;
    r = CAR(ENV);
    if (ftype == SYM_t) // trampoline
      CAR(ENV) = CDR(f);
    else {
      CAR(ENV) = miliCons(NIL, CAR(ENV));
      /* lexical bindings */
      for (p = CDR(f); LIST_P(p); p = CDR(p))
        miliDefine(CAR(CAR(p)), CDR(CAR(p)), NIL);
    }
    /* dynamic bindings */
    for (p = miliCar(CDR(CAR(f))), q = args; LIST_P(p) && LIST_P(q);
         p = CDR(p), q = CDR(q))
      miliDefine(CAR(p), macrop ? CAR(q) : miliEval(CAR(q)), T);
    if (!NIL_P(p)) // dotted pairs?
      miliDefine(p, macrop ? q : miliEval(q), T);
    /* eval body */
    for (q = CDR(CDR(CAR(f))); LIST_P(CDR(q)); q = CDR(q))
      miliEval(CAR(q));
    p = miliEval(CAR(q));
    /* there may be one dotted pair at the end of body, neglect it */
    CAR(ENV) = r; // recover env
    return p; // return the value of the last expression in body
  }
  default:
    return errRef(ERR_TYPE);
  }
}

Ref miliEqual(Ref x, Ref y) {
  RefType type = getRefType(x);
  if (!testRefType(y, type))
    return NIL;
  switch (type) {
  case REF_NIL:
    return T;
  case REF_ADDR:
    return (x == y) ? T : NIL;
  case REF_LIST: {
    Ref p = x, q = y;
    for (; LIST_P(p) && LIST_P(q); p = CDR(p), q = CDR(q))
      if (miliEqual(CAR(p), CAR(q)) == NIL)
        return NIL;
    return miliEqual(p, q); // maybe dotted pairs?
  }
  case REF_SYMBOL:
    return (UINT(x) == UINT(y)) ? NIL : T;
  default:
    return errRef(ERR_TYPE);
  }
}

Ref mili_quote(Ref exp) { return miliCar(exp); }

#define MILI_PRIM_1(name, f)                                                   \
  Ref mili_##name(Ref exp) { return f(miliEval(miliCar(exp))); }

MILI_PRIM_1(eval, miliEval)
MILI_PRIM_1(car, miliCar)
MILI_PRIM_1(cdr, miliCdr)
MILI_PRIM_1(freeze, miliFreeze)

#define MILI_PRIM_2(name, f)                                                   \
  Ref mili_##name(Ref exp) {                                                   \
    return f(miliEval(miliCar(exp)), miliEval(miliCar(miliCdr(exp))));         \
  }

MILI_PRIM_2(equal, miliEqual)
MILI_PRIM_2(cons, miliCons)

Ref mili_set(Ref exp) {
  Ref key = miliEval(miliCar(exp));
  Ref value = miliEval(miliCar(miliCdr(exp)));
  return miliSet(key, value);
}

Ref mili_define(Ref exp) {
  Ref key = miliEval(miliCar(exp));
  Ref value = miliEval(miliCar(miliCdr(exp)));
  return miliDefine(key, value, miliEval(miliCdr(miliCdr(exp))));
}

Ref mili_atom(Ref exp) {
  Ref x = miliEval(miliCar(exp));
  switch (getRefType(x)) {
  case REF_NIL:
  case REF_LIST:
    return NIL;
  default:
    return x;
  }
}

Ref mili_list(Ref exp) {
  Ref p = exp;
  Node n = {NIL, NIL};
  Ref q = makeRef((Ref)&n, REF_LIST);
  for (; LIST_P(p); p = CDR(p)) {
    CDR(q) = miliCons(miliEval(miliCar(p)), NIL);
    q = CDR(q);
  }
  CDR(q) = miliEval(p); // dotted pair
  return n.cdr;
}

Ref mili_if(Ref exp) {
  return miliEval((NIL_P(miliEval(CAR(exp)))) ? CAR(CDR(CDR(exp)))
                                              : CAR(CDR(exp)));
}

#define MILI_ARITHMETICS(op)                                                   \
  if (LIST_P(exp)) {                                                           \
    Ref x = miliEval(CAR(exp));                                                \
    if (!testRefType(x, REF_ADDR))                                             \
      return errRef(ERR_TYPE);                                                 \
    unsigned long res = UINT(x);                                               \
    for (Ref j = CDR(exp); LIST_P(j); j = CDR(j)) {                            \
      x = miliEval(CAR(j));                                                    \
      if (!testRefType(x, REF_ADDR))                                           \
        return errRef(ERR_TYPE);                                               \
      res op## = UINT(x);                                                      \
    }                                                                          \
    return makeRef((Ref)res, REF_ADDR);                                        \
  } else                                                                       \
    return errRef(ERR_TYPE)

Ref mili_add(Ref exp) { MILI_ARITHMETICS(+); }
Ref mili_sub(Ref exp) { MILI_ARITHMETICS(-); }
Ref mili_mul(Ref exp) { MILI_ARITHMETICS(*); }
Ref mili_div(Ref exp) { MILI_ARITHMETICS(/); }

static const char reschars[] = " \v\t\n.()";
static const char numleads[] = "0123456789";
static const char wsp[] = " \v\t\n";
char *miliParse(char *line, List parent, int limit) {
#define SHIFT(v)                                                               \
  ({                                                                           \
    if (!NIL_P(parent->car)) {                                                 \
      parent->cdr = miliCons(NIL, NIL);                                        \
      parent = LIST(parent->cdr);                                              \
    }                                                                          \
    parent->car = v;                                                           \
  })

  while (*line != '\0' && limit-- != 0) {
    while (strchr(wsp, *line))
      line++;
    if (*line == '\'') {
      Ref x = miliCons(makeRef((Ref)SYM_quote, REF_SYMBOL), NIL);
      SHIFT(x);
      line++;
      line = miliParse(line, LIST(x), 1);
    } else if (*line == '.') {
      Ref x = miliCons(NIL, NIL);
      line++;
      line = miliParse(line, LIST(x), 1);
      parent->cdr = CAR(x);
    } else if (*line == '(') {
      Ref x = miliCons(NIL, NIL);
      SHIFT(x);
      line++;
      line = miliParse(line, LIST(x), -1);
    } else if (*line == ')') {
      return ++line;
    } else {
      Ref val;
      if (strchr(numleads, *line))
        val = makeRef((Ref)strtoul(line, &line, 0), REF_ADDR);
      else {
        char *bgn = line;
        for (line++; !strchr(reschars, *line); line++)
          ;
        char *s = strndup(bgn, (int)(line - bgn));
        val = miliIntern(s);
        free(s);
      }
      SHIFT(val);
    }
  }
  return line;
}

Ref miliReadLine() {
  char *line = NULL;
  size_t n;
  printf("\n(mili) ");
  if (getline(&line, &n, stdin) < 0)
    exit(0);
  Node root = {NIL, NIL};
  miliParse(line, &root, -1);
  free(line);
  return root.car;
}

Ref miliPrintUm(Ref value) {
  switch (getRefType(value)) {
  case REF_NIL:
    printf("nil");
    break;
  case REF_LIST:
    if (marked[heapPos(value)]) {
      marked[heapPos(value)] -= 1; // entry once
      printf("(");
      Ref p = value;
      miliPrintUm(CAR(p));
      for (p = CDR(p); LIST_P(p); p = CDR(p)) {
        printf(" ");
        if (marked[heapPos(p)]) {
          marked[heapPos(p)] -= 1; // entry once
          miliPrintUm(CAR(p));
        } else
          printf("@[%#lx]", heapPos(value));
      }
      if (!NIL_P(p)) { // Dotted pairs
        printf(" . ");
        miliPrintUm(p);
      }
      printf(")");
    } else
      printf("@[%#lx]", heapPos(value));
    break;
  case REF_SYMBOL:
    printf("%s", miliSymbolName(value));
    break;
  case REF_ADDR:
    printf("%#lx", (unsigned long)unRef(value));
    break;
  case REF_ERROR:
    printf("<#ERROR>");
    break;
  default:
    printf("<#?>");
    break;
  }
  return NIL;
}

Ref miliPrint(Ref value) {
  mark(value);
  return miliPrintUm(value);
}

void miliPrimitive(char *name, Ref (*f)(Ref)) {
  miliSet(miliIntern(name), makeRef((Ref)f, REF_ADDR));
}

int main(int argc, char *argv[]) {
  /* Initialize heap */
  memset(marked, 0, sizeof(marked));
  for (fltop = 0; fltop < HEAP_SIZE - 1; fltop++)
    freelist[fltop] = HEAP_SIZE - 1 - fltop;
  /* Initialize symbol table */
  symtbl[SYM_quote] = "quote";
  symtbl[SYM_t] = "t";
  symtbl[SYM_m] = "m";
  symtbl[SYM_f] = "f";
  symtbl[SYM_env] = "env";
  symcnt = SYMCNT;
  /* Initialize environment */
  CAR(ENV) = miliCons(NIL, NIL);
  CDR(ENV) = NIL;
  miliSet(makeRef(SYM_env, REF_SYMBOL), makeRef(ENV, REF_LIST));
  miliSet(makeRef(SYM_t, REF_SYMBOL), makeRef(SYM_t, REF_SYMBOL));
#define PRIM(name) miliPrimitive(#name, mili_##name)
  PRIM(quote);
  PRIM(eval);
  PRIM(cons);
  PRIM(list);
  PRIM(car);
  PRIM(cdr);
  PRIM(equal);
  PRIM(if);
  PRIM(atom);
  PRIM(set);
  PRIM(define);
  PRIM(freeze);
  miliPrimitive("+", mili_add);
  miliPrimitive("-", mili_sub);
  miliPrimitive("*", mili_mul);
  miliPrimitive("/", mili_div);
  /* REPL */
  for (;;)
    miliPrint(miliEval(miliReadLine()));
  return 0;
}
