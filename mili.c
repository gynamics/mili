/** mili.c: MIni LIsp in C
 *
 * A Scheme-style Lisp implementation in about 650 lines.
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

static inline Ref makeRef(Ref ptr, RefType type) {
  return (Ref)((ptr & ~TAGTYPE_MASK) | ((uintptr_t)type << TAGPTR_BITS));
}

static inline void *unRef(Ref ref) { return (void *)(ref & TAGPTR_MASK); }

#define STACK_SIZE 1024
static volatile Ref fret; // function return value
static Ref stack[STACK_SIZE];
static int sp;
static inline void miliPush(Ref v) { stack[++sp] = v; }
static inline Ref miliPop() { return stack[--sp]; }
#define V(n) stack[sp - n]
static inline Ref miliCall_1(void (*f)(), Ref a0) {
  return miliPush(a0), f(), miliPop(), fret;
}
static inline Ref miliCall_2(void (*f)(), Ref a0, Ref a1) {
  miliPush(a1), miliPush(a0), f();
  return miliPop(), miliPop(), fret;
}
static inline Ref miliCall_3(void (*f)(), Ref a0, Ref a1, Ref a2) {
  miliPush(a2), miliPush(a1), miliPush(a0), f();
  return miliPop(), miliPop(), miliPop(), fret;
}

typedef enum {
  ERR_EVAL,
  ERR_TYPE,
} ErrType;

Ref miliPrint(Ref exp);
static inline Ref errRef(ErrType err) {
  printf("Error %d\n", err);
  printf("Call Trace:\n");
  for (int i = sp; i > 0 && sp - i < 8; i--)
    printf("%d: ", i), miliPrint(stack[i]), printf("\n");
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

#define TAGMARK_BITS 2
#define TAGMARK_OFFSET (TAGPTR_BITS + TAGTYPE_BITS)
#define TAGMARK_MASK (TAG_MASK << TAGTYPE_BITS)
typedef enum {
  MARK_00,
  MARK_01,
  MARK_10,
  MARK_11,
} MarkType;
static inline void setMark(List l, MarkType m) {
  l->car = ((l->car & ~TAGMARK_MASK) | ((uintptr_t)m << TAGMARK_OFFSET));
}
#define HEAP_SIZE 4096
static Node heap[HEAP_SIZE];
static volatile List freelist;
static inline size_t heapPos(Ref x) { return LIST(x) - heap; }
int testMark(int x, MarkType m) {
  return (((uintptr_t)heap[x].car >> TAGMARK_OFFSET) == m);
}
void mark(Ref x) {
  if (LIST_P(x)) {
    size_t pos = heapPos(x);
    if (!testMark(pos, MARK_11)) {
      if (testMark(pos, MARK_01))
        setMark(LIST(x), MARK_11);
      else {
        setMark(LIST(x), MARK_01);
        mark(CAR(x));
        mark(CDR(x));
      }
    }
  }
}

#define ENV ((Ref)(heap) | ((uintptr_t)REF_LIST << TAGPTR_BITS))
void miliGC() {
#ifdef DEBUG
  int count = 0;
  printf("\nGC triggered.\n");
#endif
  mark(fret);
  mark(ENV);
  for (int i = sp; i >= 0; --i)
    mark(stack[i]);
  for (int i = 0; i < HEAP_SIZE; i++)
    if (testMark(i, MARK_00)) { // recycle nodes
      setMark((List)&heap[i], MARK_00);
      heap[i].cdr = (Ref)freelist;
      freelist = &heap[i];
#ifdef DEBUG
      ++count;
#endif
    } else
      setMark((List)&heap[i], MARK_00);
#ifdef DEBUG
  printf("\nGC end, %d nodes recycled.\n", count);
#endif
}

void _miliCons() {
  if (freelist == NIL) // freelist expired, trigger GC
    miliGC();
  List x = freelist;
  freelist = (List)freelist->cdr;
  x->car = V(0);
  x->cdr = V(1);
  fret = makeRef((Ref)x, REF_LIST);
}
Ref miliCons(Ref car, Ref cdr) { return miliCall_2(_miliCons, car, cdr), fret; }

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
static inline char *miliSymbolName(Ref id) { return symtbl[UINT(id)]; }
Ref miliIntern(char *s) {
  for (int i = 0; i < symcnt; ++i)
    if (strcmp(s, symtbl[i]) == 0)
      return makeRef((Ref)i, REF_SYMBOL);
  /* not found, insert it */
  symtbl[symcnt++] = strdup(s);
  return makeRef((Ref)(symcnt - 1), REF_SYMBOL);
}

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
  p = miliGetLocal(key);
  if (p == NIL) {
    for (q = CDR(ENV); LIST_P(q); q = CDR(q))
      if (key == CAR(CAR(q)))
        return CAR(q);
    return NIL;
  } else
    return p;
}

void _miliApply();
void _miliEval() {
#define exp V(0)
#ifdef DEBUG
  static int d = 0;
  printf("Eval{%d} ", d++), miliPrint(exp);
  printf(" :: type%d\n", getRefType(exp));
  // printf("\n ENV: "), miliPrint(ENV), printf("\n\n");
#endif
  switch (getRefType(exp)) {
  case REF_NIL:
    fret = NIL;
    break;
  case REF_LIST:
    if (NIL_P(CAR(exp)))
      fret = NIL; // () => nil
    else
      miliCall_2(_miliApply, CAR(exp), CDR(exp));
    break;
  case REF_SYMBOL:
    fret = miliCdr(miliGet(exp));
    break;
  case REF_ADDR:
    fret = exp;
    break;
  default:
    fret = errRef(ERR_EVAL);
  }
#undef exp
#ifdef DEBUG
  printf("{%d} => ", --d), miliPrint(fret), printf("\n");
#endif
}
Ref miliEval(Ref exp) { return miliCall_1(_miliEval, exp), fret; }

void _miliSet() {
#define key V(0)
#define value V(1)
  if (!testRefType(key, REF_SYMBOL))
    fret = errRef(ERR_TYPE);
  else {
    Ref cell = miliGetLocal(key);
    if (NIL_P(cell))
      CDR(ENV) = miliCons(miliCons(key, value), CDR(ENV));
    else
      CDR(cell) = value;
    fret = value;
  }
#undef key
#undef value
}
Ref miliSet(Ref key, Ref value) {
  return miliCall_2(_miliSet, key, value), fret;
}

void _miliDefine() {
#define key V(0)
#define value V(1)
#define mut V(2)
  if (!testRefType(key, REF_SYMBOL))
    fret = errRef(ERR_TYPE);
  else {
    Ref cell = miliGetLocal(key);
    if (NIL_P(cell)) {
      CAR(CAR(ENV)) = miliCons(miliCons(key, value), CAR(CAR(ENV)));
      fret = value;
    } else if (NIL_P(mut))
      fret = CDR(cell);
    else
      fret = (CDR(cell) = value);
  }
#undef key
#undef value
#undef mut
}
Ref miliDefine(Ref key, Ref value, Ref mut) {
  return miliCall_3(_miliDefine, key, value, mut), fret;
}

void _miliFreeze() {
  miliPush(NIL);
#define head V(0)
#define scope V(1)
  head = miliCons(NIL, NIL);
  Ref r = head;
  for (Ref p = CAR(ENV); p != scope; p = CDR(p))
    for (Ref q = CAR(p); LIST_P(q); q = CDR(q)) {
      Ref b = CAR(q);
      // duplicate bindings are not removed but left behind
      CDR(r) = miliCons(miliCons(CAR(b), CDR(b)), NIL);
      r = CDR(r);
    }
  fret = CDR(head);
#undef head
#undef scope
  miliPop(); // head
}
Ref miliFreeze(Ref scope) { return miliCall_1(_miliFreeze, scope), fret; }

void _miliApply() {
  miliPush(NIL);
  miliPush(NIL);
#define f V(0)
#define l V(1)
#define fexp V(2)
#define args V(3)
#ifdef DEBUG
  printf("Apply "), miliPrint(fexp), printf(" "), miliPrint(args), printf("\n");
#endif
  f = miliEval(fexp);
  switch (getRefType(f)) {
  case REF_ADDR:
    fret = ((Ref (*)(Ref))unRef(f))(args);
    break;
  case REF_LIST: {
    if (!LIST_P(f) || !LIST_P(CAR(f)) ||
        !testRefType(CAR(CAR(f)), REF_SYMBOL)) {
      fret = errRef(ERR_TYPE);
      break;
    }
    int ftype = UINT(CAR(CAR(f)));
    Ref p, q, r;
    if (ftype != SYM_m) { // if it is not a macro, evaluate arguments first
      l = miliCons(NIL, NIL);
      for (p = l, q = args; LIST_P(q); p = CDR(p), q = CDR(q))
        CDR(p) = miliCons(miliEval(CAR(q)), NIL);
      if (!NIL_P(q))
        CDR(p) = miliEval(q);
      args = CDR(l);
    }
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
      miliDefine(CAR(p), CAR(q), T);
    if (!NIL_P(p)) // dotted pairs?
      miliDefine(p, q, T);
    /* eval body */
    for (q = CDR(CDR(CAR(f))); LIST_P(CDR(q)); q = CDR(q))
      miliEval(CAR(q));
    fret = miliEval(CAR(q));
    /* there may be one dotted pair at the end of body, neglect it */
    CAR(ENV) = r; // recover env
    break;        // return the value of the last expression in body
  }
  default:
    fret = errRef(ERR_TYPE);
    break;
  }
  miliPop(); // l
  miliPop(); // f
#undef fexp
#undef args
#undef l
#undef f
}
Ref miliApply(Ref f, Ref args) { return miliCall_2(_miliApply, f, args), fret; }

Ref miliEqual(Ref x, Ref y);
void _miliEqual() {
#define x V(0)
#define y V(1)
  RefType type = getRefType(x);
  if (!testRefType(y, type))
    fret = NIL;
  else
    switch (type) {
    case REF_NIL:
      fret = T;
      break;
    case REF_ADDR:
      fret = (x == y) ? T : NIL;
      break;
    case REF_LIST: {
      Ref p = x, q = y;
      for (; LIST_P(p) && LIST_P(q); p = CDR(p), q = CDR(q))
        if (miliEqual(CAR(p), CAR(q)) == NIL) {
          fret = NIL;
          break;
        }
      if (fret != NIL)
        fret = miliEqual(p, q); // maybe dotted pairs?
      break;
    }
    case REF_SYMBOL:
      fret = (UINT(x) == UINT(y)) ? NIL : T;
    default:
      fret = errRef(ERR_TYPE);
    };
#undef x
#undef y
}
Ref miliEqual(Ref x, Ref y) { return miliCall_2(_miliEqual, x, y), fret; }

Ref mili_quote(Ref exp) { return miliCar(exp); }

#define MILI_PRIM_1(name, f)                                                   \
  Ref mili_##name(Ref exp) { return f(miliEval(miliCar(exp))); }

MILI_PRIM_1(eval, miliEval)
MILI_PRIM_1(car, miliCar)
MILI_PRIM_1(cdr, miliCdr)
MILI_PRIM_1(freeze, miliFreeze)

#define MILI_PRIM_2(name, f)                                                   \
  Ref mili_##name(Ref exp) {                                                   \
    Ref arg1 = miliEval(miliCar(exp));                                         \
    Ref arg2 = miliEval(miliCar(miliCdr(exp)));                                \
    return f(arg1, arg2);                                                      \
  }

MILI_PRIM_2(equal, miliEqual)
MILI_PRIM_2(cons, miliCons)

Ref mili_set(Ref exp) {
  miliPush(NIL), miliPush(NIL);
  V(0) = miliEval(miliCar(exp));
  V(1) = miliEval(miliCar(miliCdr(exp)));
  _miliSet();
  miliPop(), miliPop();
  return fret;
}

Ref mili_define(Ref exp) {
  miliPush(NIL), miliPush(NIL), miliPush(NIL);
  V(0) = miliEval(miliCar(exp));
  V(1) = miliEval(miliCar(miliCdr(exp)));
  V(2) = miliEval(miliCdr(miliCdr(exp)));
  _miliDefine();
  miliPop(), miliPop(), miliPop();
  return fret;
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
  Ref head = miliCons(NIL, NIL);
  miliPush(head);
  Ref p = exp;
  Ref q = head;
  for (; LIST_P(p); p = CDR(p)) {
    CDR(q) = miliCons(miliEval(miliCar(p)), NIL);
    q = CDR(q);
  }
  CDR(q) = miliEval(p); // dotted pair
  miliPop();
  return CDR(head);
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
  miliPush(NIL);
#define x V(0)
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
      x = miliCons(makeRef((Ref)SYM_quote, REF_SYMBOL), NIL);
      SHIFT(x);
      line++;
      line = miliParse(line, LIST(x), 1);
    } else if (*line == '.') {
      x = miliCons(NIL, NIL);
      line++;
      line = miliParse(line, LIST(x), 1);
      parent->cdr = CAR(x);
    } else if (*line == '(') {
      x = miliCons(NIL, NIL);
      SHIFT(x);
      line++;
      line = miliParse(line, LIST(x), -1);
    } else if (*line == ')') {
      return miliPop(), ++line;
    } else {
      if (strchr(numleads, *line))
        x = makeRef((Ref)strtoul(line, &line, 0), REF_ADDR);
      else {
        char *bgn = line;
        for (line++; !strchr(reschars, *line); line++)
          ;
        char *s = strndup(bgn, (int)(line - bgn));
        x = miliIntern(s);
        free(s);
      }
      SHIFT(x);
    }
  }
#undef x
  miliPop();
  return line;
}

Ref miliReadLine() {
  char *line = NULL;
  size_t n;
  printf("\n\n(mili) ");
  if (getline(&line, &n, stdin) < 0)
    exit(0);
  Node root = {NIL, NIL};
  miliParse(line, &root, -1);
  free(line);
  return root.car;
}

Ref miliPrintValue(Ref value);
Ref miliPrintList(Ref l) {
  if (!testMark(heapPos(l), MARK_00)) {
    setMark(LIST(l), MARK_00);
    miliPrintValue(CAR(l));
    if (LIST_P(CDR(l)))
      printf(" "), miliPrintList(CDR(l));
    else if (!NIL_P(CDR(l)))
      printf(" . "), miliPrintValue(CDR(l));
  } else
    printf("#%#lx#", heapPos(l));
  return NIL;
}

Ref miliPrintValue(Ref value) {
  switch (getRefType(value)) {
  case REF_NIL:
    printf("nil");
    break;
  case REF_LIST:
    if (testMark(heapPos(value), MARK_11))
      printf("#%#lx=", heapPos(value));
    printf("(");
    miliPrintList(value);
    printf(")");
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

Ref miliPrint(Ref value) { return mark(value), miliPrintValue(value); }

void miliPrimitive(char *name, Ref (*f)(Ref)) {
  miliSet(miliIntern(name), makeRef((Ref)f, REF_ADDR));
}

int main(int argc, char *argv[]) {
  /* Initialize stack */
  sp = -1;
  /* Initialize heap */
  freelist = (List)NIL;
  for (int i = HEAP_SIZE - 1; i > 0; --i) {
    heap[i].cdr = (Ref)freelist;
    freelist = &heap[i];
  }
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
  /* A simple REPL */
  for (;;)
    miliPrint(miliEval(miliReadLine()));
  return 0;
}
