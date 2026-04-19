/** mili.c: MIni LIsp in C
 *
 * - Everything built on list
 * - Use C call stack for recursion
 * - Mixed lex/dyn environment
 * - Support 1k symbols and 4k nodes
 * - Simple mark-and-sweep GC
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
  ERR_ARGTYPE,
  ERR_ARGCOUNT,
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

typedef struct {
  Ref car;
  Ref cdr;
} Node, *List;

#define NIL ((Ref)((uintptr_t)REF_NIL << TAGPTR_BITS))
static Ref env = NIL; // ( .. ( .. (symbol . value)))
#define LIST(ref) ((List)unRef(ref))
#define CAR(ref) (LIST(ref)->car)
#define CDR(ref) (LIST(ref)->cdr)
#define UINT(ref) ((unsigned long)unRef(ref))

#define HEAP_SIZE 4096
static Node heap[HEAP_SIZE];
static int heaptop;
static int freelist[HEAP_SIZE];
static int fltop;
static uint8_t marked[HEAP_SIZE];
void mark(Ref x) {
  if (!testRefType(x, REF_LIST) || marked[x])
    return;
  marked[x] = 1;
  mark(CAR(x));
  mark(CDR(x));
}

void sweep() {
  for (int i = 0; i < heaptop; i++)
    if (!marked[i])
      freelist[fltop++] = i;
    else
      marked[i] = 0;
}

static inline List miliAllocNode() {
  if (heaptop == HEAP_SIZE) { // pool is full, trigger GC
    mark(env);
    sweep();
  }
  return &heap[(fltop > 0) ? freelist[--fltop] : heaptop++];
}

static inline Ref miliCons(Ref car, Ref cdr) {
  List x = miliAllocNode();
  x->car = car;
  x->cdr = cdr;
  return makeRef((Ref)x, REF_LIST);
}

typedef enum {
  SYM_quote,
  SYM_t,
  SYM_m,
  SYM_f,
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
  symtbl[symcnt++] = s;
  return makeRef((Ref)(symcnt - 1), REF_SYMBOL);
}

Ref miliApply(Ref fexp, Ref args);
Ref miliPrint(Ref exp, Ref zip);
Ref miliGet(Ref key, Ref scope) {
  Ref p, q;
  for (p = env; p != scope; p = CDR(p))
    for (q = CAR(p); !testRefType(q, REF_NIL); q = CDR(q))
      if (key == CAR(CAR(q)))
        return q;
  return NIL;
}

Ref miliEval(Ref exp) {
#ifdef DEBUG
  printf("Eval "), miliPrint(exp, NIL), printf(" :: type%d \n", getRefType(exp));
#endif
  switch (getRefType(exp)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    if (testRefType(CAR(exp), REF_NIL))
      return NIL; // () => nil
    else
      return miliApply(miliEval(CAR(exp)), CDR(exp));
  case REF_SYMBOL: {
    Ref v = miliGet(exp, NIL);
    return (v == NIL) ? NIL : CDR(CAR(v));
  }
  case REF_ADDR:
    return exp;
  default:
    return errRef(ERR_EVAL);
  }
}

Ref mili_eval(Ref exp) { return miliEval(miliEval(CAR(exp))); }

Ref miliSet(Ref key, Ref value, Ref scope) {
  if (!testRefType(key, REF_SYMBOL))
    return errRef(ERR_ARGTYPE);
  Ref cell = miliGet(key, scope);
  if (testRefType(cell, REF_NIL))
    CAR(env) = miliCons(miliCons(key, value), CAR(env));
  else
    CDR(CAR(cell)) = value;
  return value;
}

Ref mili_set(Ref exp) {
  Ref key = miliEval(CAR(exp));
  Ref value = miliEval(CAR(CDR(exp)));
  Ref scope = miliEval(CDR(CDR(exp)));
  return miliSet(key, value, scope);
}

Ref mili_quote(Ref exp) {
  Ref x = CAR(exp);
  return (testRefType(CDR(exp), REF_NIL)) ? x : errRef(ERR_ARGTYPE);
}

Ref miliFreeze(Ref head) {
  Node n = {NIL, NIL};
  Ref r = makeRef((Ref)&n, REF_LIST);
  for (Ref p = head; !testRefType(p, REF_NIL); p = CDR(p))
    for (Ref q = CAR(p); !testRefType(q, REF_NIL); q = CDR(q)) {
      Ref b = CAR(q);
      // duplicate bindings are not removed but left behind
      CDR(r) = miliCons(miliCons(CAR(b), CDR(b)), NIL);
      r = CDR(r);
    }
  return n.cdr;
}

Ref mili_freeze(Ref exp) { return miliFreeze(env); }

Ref mili_list(Ref exp) {
  Ref p = exp;
  Node n = {NIL, NIL};
  Ref q = makeRef((Ref)&n, REF_LIST);
  for (; testRefType(p, REF_LIST); p = CDR(p)) {
    CDR(q) = miliCons(miliEval(CAR(p)), NIL);
    q = CDR(q);
  }
  return n.cdr;
}

Ref miliDefine(Ref key, Ref value) {
  if (!testRefType(key, REF_SYMBOL))
    return errRef(ERR_ARGTYPE);
  Ref next = (env == NIL) ? NIL : CDR(env);
  Ref cell = miliGet(key, next);
  if (testRefType(cell, REF_NIL)) {
    CAR(env) = miliCons(miliCons(key, value), CAR(env));
    return value;
  } else
    return CDR(CAR(cell)); // never override existing dynamic bindings
}

Ref mili_define(Ref exp) {
  Ref key = miliEval(CAR(exp));
  Ref value = miliEval(CAR(CDR(exp)));
  return miliDefine(key, value);
}

Ref miliApply(Ref f, Ref args) {
#ifdef DEBUG
  printf("Apply "), miliPrint(f, NIL);
  printf(" "), miliPrint(args, NIL), printf("\n");
#endif
  switch (getRefType(f)) {
  case REF_ADDR:
    return ((Ref (*)(Ref))unRef(f))(args);
  case REF_LIST: {
    unsigned long ftype = UINT(CAR(CAR(f)));
    int macrop = (ftype == SYM_m);
    Ref p, q, r;
    r = env;
    env = miliCons(NIL, env);
    /* lexical bindings */
    for (p = CDR(f); !testRefType(p, REF_NIL); p = CDR(p))
      miliDefine(CAR(CAR(p)), CDR(CAR(p)));
    /* dynamic bindings */
    for (p = CAR(CDR(CAR(f))), q = args;
         testRefType(p, REF_LIST) && testRefType(q, REF_LIST);
         p = CDR(p), q = CDR(q))
      miliSet(CAR(p), macrop ? CAR(q) : miliEval(CAR(q)), r);
    if (!testRefType(p, REF_NIL)) // dotted pairs?
      miliSet(p, macrop ? q : miliEval(q), r);
    /* eval body */
    for (q = CDR(CDR(CAR(f))); testRefType(CDR(q), REF_LIST); q = CDR(q))
      miliEval(CAR(q));
    p = miliEval(CAR(q));
    /* return */
    env = CDR(env);
    return p;
  }
  default:
    return errRef(ERR_ARGTYPE);
  }
}

Ref mili_apply(Ref exp) { return miliApply(CAR(exp), CAR(CDR(exp))); }

Ref mili_atom(Ref exp) {
  Ref x = miliEval(CAR(exp));
  switch (getRefType(x)) {
  case REF_NIL:
  case REF_LIST:
    return NIL;
  default:
    return x;
  }
}

#define T ((Ref)((uintptr_t)SYM_t | ((uintptr_t)REF_SYMBOL << TAGPTR_BITS)))
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
    for (; testRefType(p, REF_LIST) && testRefType(q, REF_LIST);
         p = CDR(p), q = CDR(q))
      if (miliEqual(CAR(p), CAR(q)) == NIL)
        return NIL;
    return miliEqual(p, q); // maybe dotted pairs?
  }
  case REF_SYMBOL:
    return (UINT(x) == UINT(y)) ? NIL : T;
  default:
    return errRef(ERR_ARGTYPE);
  }
}

Ref mili_equal(Ref exp) { return miliEqual(CAR(exp), CAR(CDR(exp))); }

Ref mili_cons(Ref exp) {
  return miliCons(miliEval(CAR(exp)), miliEval(CAR(CDR(exp))));
}

Ref mili_car(Ref exp) {
  Ref x = miliEval(CAR(exp));
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CAR(x);
  default:
    return errRef(ERR_ARGTYPE);
  }
}

Ref mili_cdr(Ref exp) {
  Ref x = miliEval(CAR(exp));
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CDR(x);
  default:
    return errRef(ERR_ARGTYPE);
  }
}

Ref mili_if(Ref exp) {
  return miliEval((testRefType(miliEval(CAR(exp)), REF_NIL))
                      ? CAR(CDR(CDR(exp)))
                      : CAR(CDR(exp)));
}

#define MILI_ARITHMETICS(init, start, op)                                      \
  unsigned long res = init;                                                    \
  for (Ref j = start; !testRefType(j, REF_NIL); j = CDR(j)) {                  \
    Ref x = miliEval(CAR(j));                                                  \
    if (!testRefType(x, REF_ADDR))                                             \
      return errRef(ERR_ARGTYPE);                                              \
    res op## = UINT(x);                                                        \
  }                                                                            \
  return makeRef((Ref)res, REF_ADDR)

#define MILI_ARITHMETICS_1(op)                                                 \
  if (!testRefType(exp, REF_NIL)) {                                            \
    MILI_ARITHMETICS(UINT(CAR(exp)), CDR(exp), op);                            \
  } else                                                                       \
    return errRef(ERR_ARGTYPE)

Ref mili_add(Ref exp) { MILI_ARITHMETICS(0, exp, +); }
Ref mili_sub(Ref exp) { MILI_ARITHMETICS_1(-); }
Ref mili_mul(Ref exp) { MILI_ARITHMETICS(1, exp, *); }
Ref mili_div(Ref exp) { MILI_ARITHMETICS_1(/); }

static const char reschars[] = " \v\t\n.()";
static const char numlead[] = "0123456789";
static const char wsp[] = " \v\t\n";
#define SHIFT(v)                                                               \
  ({                                                                           \
    if (!testRefType(parent->car, REF_NIL)) {                                  \
      parent->cdr = miliCons(NIL, NIL);                                        \
      parent = LIST(parent->cdr);                                              \
    }                                                                          \
    parent->car = v;                                                           \
  })

char *miliParse(char *line, List parent, int limit) {
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
      if (strchr(numlead, *line))
        val = makeRef((Ref)strtoul(line, &line, 0), REF_ADDR);
      else {
        char *bgn = line;
        for (line++; !strchr(reschars, *line); line++)
          ;
        val = miliIntern(strndup(bgn, (int)(line - bgn)));
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
  getline(&line, &n, stdin);
  Node root = {NIL, NIL};
  miliParse(line, &root, -1);
  free(line);
  return root.car;
}

Ref miliFind(Ref value, Ref l) {
  Ref j;
  for (j = l; !testRefType(j, REF_NIL); j = CDR(j))
    if (value == CAR(j))
      return j;
  return NIL;
}

Ref miliPrint(Ref value, Ref zip) {
  switch (getRefType(value)) {
  case REF_NIL:
    printf("nil");
    break;
  case REF_LIST:
    /* This can not prevent reentry a parent node, repeats may still exist. */
    if (zip != NIL && miliFind(value, zip) != NIL) {
      printf("*");
      break;
    }
    Ref nz = miliCons(value, zip);
    printf("(");
    Ref p = value;
    for (; testRefType(CDR(p), REF_LIST); p = CDR(p)) {
      miliPrint(CAR(p), nz);
      printf(" ");
    }
    miliPrint(CAR(p), nz);
    if (!testRefType(CDR(p), REF_NIL)) { // Dotted pairs
      printf(" . ");
      miliPrint(CDR(p), nz);
    }
    printf(")");
    break;
  case REF_SYMBOL:
    printf("%s", miliSymbolName(value));
    break;
  case REF_ADDR:
    printf("%p", (void *)unRef(value));
    break;
  default:
    printf("Eval Error!\n");
    break;
  }
  return NIL;
}

void miliPrimitive(char *name, Ref (*f)(Ref)) {
  miliDefine(miliIntern(name), makeRef((Ref)f, REF_ADDR));
}

int main(int argc, char *argv[]) {
  /* Initialize heap */
  memset(marked, 0, sizeof(marked));
  heaptop = 0;
  fltop = 0;
  /* Initialize symbol table */
  symtbl[SYM_quote] = "quote";
  symtbl[SYM_t] = "t";
  symtbl[SYM_m] = "m";
  symtbl[SYM_f] = "f";
  symcnt = SYMCNT;
  /* Initialize environment */
  env = miliCons(NIL, NIL);
#define PRIM(name) miliPrimitive(#name, mili_##name)
  PRIM(quote);
  PRIM(eval);
  PRIM(apply);
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
    miliPrint(miliEval(miliReadLine()), NIL);
  return 0;
}
