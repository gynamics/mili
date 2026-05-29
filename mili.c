/** mili.c: MIni LIsp in C
 *
 * A Scheme-style Lisp implementation in about 700 lines.
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
#define TYPE_BITS 3
#define TYPE_MASK (TAG_MASK ^ (TAG_MASK << TYPE_BITS))
typedef enum {
  REF_NIL,
  REF_LIST,
  REF_SYMBOL,
  REF_ADDR,
  REF_ERROR,
} RefType;

#define INLINE static inline
INLINE Ref makeRef(Ref ptr, RefType type) {
  return (Ref)((ptr & ~TYPE_MASK) | ((uintptr_t)type << TAGPTR_BITS));
}

INLINE void *unRef(Ref ref) { return (void *)(ref & TAGPTR_MASK); }

INLINE RefType getRefType(Ref ref) {
  return (RefType)((ref & TYPE_MASK) >> (TAGPTR_BITS));
}

INLINE int testRefType(Ref ref, RefType type) {
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

#define STACK_SIZE 1024
static Ref fret; // function return value
static Ref stack[STACK_SIZE];
static int sp;
INLINE void miliPush(Ref v) { stack[++sp] = v; }
INLINE void miliPop(int n) {
  while (n-- > 0)
    stack[sp--] = NIL;
}
#define V(n) stack[sp - n]

typedef enum {
  ERR_EVAL,
  ERR_TYPE,
} ErrType;

INLINE Ref miliPrint(Ref exp);
INLINE Ref errRef(ErrType err, char *errname, int n) {
  printf("Error %s @ line %d\n", errname, n);
  printf("Call Trace:\n");
  for (int i = sp; i > 0 && sp - i < 8; i--)
    printf("%d: ", i), miliPrint(stack[i]), printf("\n");
  return (Ref)(((uintptr_t)REF_ERROR << TAGPTR_BITS) | (uintptr_t)err);
}
#define ERRREF(err) errRef(err, #err, __LINE__)

Ref miliCar(Ref x) {
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CAR(x);
  default:
    return ERRREF(ERR_TYPE);
  }
}

Ref miliCdr(Ref x) {
  switch (getRefType(x)) {
  case REF_NIL:
    return NIL;
  case REF_LIST:
    return CDR(x);
  default:
    return ERRREF(ERR_TYPE);
  }
}

#define MARK_BITS 2
#define MARK_OFFSET (TAGPTR_BITS + TYPE_BITS)
#define MARK_MASK (TAG_MASK << TYPE_BITS)
typedef enum {
  MARK_00,
  MARK_01,
  MARK_10,
  MARK_11,
} MarkType;
INLINE void setMark(List l, MarkType m) {
  l->car = ((l->car & ~MARK_MASK) | ((uintptr_t)m << MARK_OFFSET));
}
#define HEAP_SIZE 4096
static Node heap[HEAP_SIZE];
static volatile List freelist;
INLINE size_t heapPos(Ref x) { return LIST(x) - heap; }
int testMark(int x, MarkType m) {
  return (((uintptr_t)heap[x].car >> MARK_OFFSET) == m);
}
/** 00 => no ref; 01 => strong ref; 11 => weak ref */
void markTree(Ref x) {
  if (LIST_P(x)) {
    size_t pos = heapPos(x);
    if (!testMark(pos, MARK_11)) {
      if (testMark(pos, MARK_01))
        setMark(LIST(x), MARK_11);
      else {
        setMark(LIST(x), MARK_01);
        markTree(CAR(x));
        markTree(CDR(x));
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
  markTree(fret);
  markTree(ENV);
  for (int i = sp; i >= 0; --i)
    markTree(stack[i]);
  for (int i = 1; i < HEAP_SIZE; i++)
    if (testMark(i, MARK_00)) { // recycle nodes
#ifdef DEBUG
      ++count;
      printf("Collect node #%d\n", i);
#endif
      heap[i].cdr = (Ref)freelist;
      freelist = &heap[i];
    } else
      setMark((List)&heap[i], MARK_00);
#ifdef DEBUG
  printf("\nGC end, %d nodes recycled.\n", count);
#endif
}

Ref miliCons(Ref car, Ref cdr) {
  if (freelist == NIL) // freelist expired, trigger GC
    miliGC();
  List x = freelist;
  freelist = (List)freelist->cdr;
  x->car = car;
  x->cdr = cdr;
  return makeRef((Ref)x, REF_LIST);
}

typedef enum {
  SYM_backquote,
  SYM_comma,
  SYM_quote,
  SYM_t,
  SYM_m,
  SYM_f,
  SYM_env,
  SYMCNT,
} PreDefinedSymbols;

static char *symtbl[1024];
static int symcnt;
INLINE char *miliSymbolName(Ref id) { return symtbl[UINT(id)]; }
Ref miliIntern(char *s) {
  for (int i = 0; i < symcnt; ++i)
    if (strcmp(s, symtbl[i]) == 0)
      return makeRef((Ref)i, REF_SYMBOL);
  /* not found, insert it */
  symtbl[symcnt++] = strdup(s);
  return makeRef((Ref)(symcnt - 1), REF_SYMBOL);
}

Ref miliGetLocal(Ref key) {
  Ref q;
  for (q = miliCar(CAR(ENV)); LIST_P(q); q = CDR(q))
    if (key == CAR(CAR(q)))
      return CAR(q);
  return NIL;
}

Ref miliGetTemp(Ref key) {
  Ref p, q;
  for (p = CAR(ENV); LIST_P(p); p = CDR(p))
    for (q = CAR(p); LIST_P(q); q = CDR(q))
      if (key == CAR(CAR(q)))
        return CAR(q);
  return NIL;
}

Ref miliGet(Ref key) {
  Ref p, q;
  p = miliGetTemp(key);
  if (p == NIL) {
    for (q = CDR(ENV); LIST_P(q); q = CDR(q))
      if (key == CAR(CAR(q)))
        return CAR(q);
    return NIL;
  } else
    return p;
}

Ref miliApply(Ref exp);
Ref miliEval(Ref exp) {
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
    fret = NIL_P(CAR(exp)) ? NIL : miliApply(exp);
    break;
  case REF_SYMBOL:
    fret = miliCdr(miliGet(exp));
    break;
  case REF_ADDR:
    fret = exp;
    break;
  default:
    fret = ERRREF(ERR_EVAL);
  }
#undef exp
#ifdef DEBUG
  printf("{%d} => ", --d), miliPrint(fret), printf("\n");
#endif
  return fret;
}

Ref miliSet(Ref key, Ref value) {
  if (!testRefType(key, REF_SYMBOL))
    fret = ERRREF(ERR_TYPE);
  else {
    Ref cell = miliGetTemp(key);
    if (NIL_P(cell)) {
      miliPush(miliCons(key, value));
      CDR(ENV) = miliCons(V(0), CDR(ENV));
      miliPop(1);
    } else
      CDR(cell) = value;
    fret = value;
  }
  return fret;
}

Ref miliDefine(Ref key, Ref value, Ref mut) {
  if (!testRefType(key, REF_SYMBOL))
    fret = ERRREF(ERR_TYPE);
  else {
    Ref cell = miliGetLocal(key);
    if (NIL_P(cell)) {
      miliPush(miliCons(key, value));
      CAR(CAR(ENV)) = miliCons(V(0), CAR(CAR(ENV)));
      miliPop(1);
      fret = value;
    } else if (NIL_P(mut))
      fret = CDR(cell);
    else
      fret = (CDR(cell) = value);
  }
  return fret;
}

Ref miliFreeze(Ref scope) {
  CAR(ENV) = miliCons(NIL, CAR(ENV));
  for (Ref p = CAR(ENV); p != scope; p = CDR(p))
    for (Ref q = CAR(p); LIST_P(q); q = CDR(q))
      miliDefine(CAR(CAR(q)), CDR(CAR(q)), T);
  fret = CAR(CAR(ENV));
  CAR(ENV) = CDR(CAR(ENV));
  return fret;
}

Ref mili_list(Ref exp) {
  Ref head = miliCons(NIL, NIL);
  miliPush(head);
  miliPush(exp);
  miliPush(NIL);
#define x V(0)
  Ref p = exp;
  Ref q = head;
  for (; LIST_P(p); p = CDR(p)) {
    x = miliEval(miliCar(p));
    CDR(q) = miliCons(x, NIL);
    q = CDR(q);
  }
  CDR(q) = miliEval(p); // dotted pair
#undef x
  miliPop(3);
  return CDR(head);
}

Ref miliApply(Ref exp) {
  sp += 4;
#define f V(0)
#define l V(1)
#define x V(2)
#define r V(3)
  f = miliEval(miliCar(exp));
  l = miliCdr(exp);
#ifdef DEBUG
  printf("Apply "), miliPrint(miliCar(exp)), printf(" "), miliPrint(l), printf("\n");
#endif
  switch (getRefType(f)) {
  case REF_ADDR:
    fret = ((Ref (*)(Ref))unRef(f))(l);
    break;
  case REF_LIST: {
    if (!LIST_P(f) || !LIST_P(CAR(f)) ||
        !testRefType(CAR(CAR(f)), REF_SYMBOL)) {
      fret = ERRREF(ERR_TYPE);
      break;
    }
    int ftype = UINT(CAR(CAR(f)));
    Ref p, q;
    if (ftype != SYM_m) // if it is not a macro, evaluate arguments first
      l = mili_list(l);
    r = CAR(ENV);
    if (ftype == SYM_t) { // trampoline
      if (CDR(f))
        CAR(ENV) = CDR(f);
    } else {
      CAR(ENV) = miliCons(NIL, CAR(ENV));
      /* lexical bindings */
      for (p = CDR(f); LIST_P(p); p = CDR(p))
        miliDefine(CAR(CAR(p)), CDR(CAR(p)), NIL);
    }
    /* dynamic bindings */
    for (p = miliCar(CDR(CAR(f))), q = l; LIST_P(p) && LIST_P(q);
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
    fret = ERRREF(ERR_TYPE);
    break;
  }
  miliPop(4);
#undef r
#undef x
#undef l
#undef f
  return fret;
}

Ref miliEqual(Ref x, Ref y) {
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
      fret = ERRREF(ERR_TYPE);
    };
  return fret;
}

Ref miliAtom(Ref exp) {
  Ref x = miliEval(miliCar(exp));
  switch (getRefType(x)) {
  case REF_NIL:
  case REF_LIST:
    return NIL;
  default:
    return x;
  }
}

Ref mili_quote(Ref exp) { return miliCar(exp); }

#define MILI_PRIM_1(name, f)                                                   \
  Ref mili_##name(Ref exp) {                                                   \
    ++sp;                                                                      \
    V(0) = miliEval(miliCar(exp));                                             \
    fret = f(V(0));                                                            \
    miliPop(1);                                                                \
    return fret;                                                               \
  }

MILI_PRIM_1(car, miliCar)
MILI_PRIM_1(cdr, miliCdr)
MILI_PRIM_1(atom, miliAtom)
MILI_PRIM_1(eval, miliEval)
MILI_PRIM_1(freeze, miliFreeze)

#define MILI_PRIM_2(name, f)                                                   \
  Ref mili_##name(Ref exp) {                                                   \
    sp += 2;                                                                   \
    V(0) = miliEval(miliCar(exp));                                             \
    V(1) = miliEval(miliCar(miliCdr(exp)));                                    \
    fret = f(V(0), V(1));                                                      \
    miliPop(2);                                                                \
    return fret;                                                               \
  }

MILI_PRIM_2(equal, miliEqual)
MILI_PRIM_2(cons, miliCons)
MILI_PRIM_2(set, miliSet)

Ref mili_define(Ref exp) {
  sp += 3;
  V(0) = miliEval(miliCar(exp));
  V(1) = miliEval(miliCar(miliCdr(exp)));
  V(2) = miliEval(miliCdr(miliCdr(exp)));
  fret = miliDefine(V(0), V(1), V(2));
  miliPop(3);
  return fret;
}

Ref mili_if(Ref exp) {
  return miliEval((NIL_P(miliEval(miliCar(exp))))
                      ? miliCar(miliCdr(miliCdr(exp)))
                      : miliCar(miliCdr(exp)));
}

#define MILI_ARITHMETICS(op)                                                   \
  if (LIST_P(exp)) {                                                           \
    Ref x = miliEval(CAR(exp));                                                \
    if (!testRefType(x, REF_ADDR))                                             \
      return ERRREF(ERR_TYPE);                                                 \
    unsigned long res = UINT(x);                                               \
    for (Ref j = CDR(exp); LIST_P(j); j = CDR(j)) {                            \
      x = miliEval(CAR(j));                                                    \
      if (!testRefType(x, REF_ADDR))                                           \
        return ERRREF(ERR_TYPE);                                               \
      res op## = UINT(x);                                                      \
    }                                                                          \
    return makeRef((Ref)res, REF_ADDR);                                        \
  } else                                                                       \
    return ERRREF(ERR_TYPE)

Ref mili_add(Ref exp) { MILI_ARITHMETICS(+); }
Ref mili_sub(Ref exp) { MILI_ARITHMETICS(-); }
Ref mili_mul(Ref exp) { MILI_ARITHMETICS(*); }
Ref mili_div(Ref exp) { MILI_ARITHMETICS(/); }

static const char reschars[] = " \v\t\n.()";
static const char numleads[] = "0123456789";
static const char wsp[] = " \v\t\n";
static int parser_depth = 0;
static char *parser_line = NULL;
static char *line = NULL;

void miliReadLine(char *prompt) {
  size_t n = 0;
  printf("\n%s", prompt);
  if (getline(&parser_line, &n, stdin) < 0)
    exit(0);
  line = parser_line;
}

int miliParse(List parent, int limit) {
  ++parser_depth;
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

  while (limit-- != 0) {
    while (*line != '\0' && strchr(wsp, *line))
      line++;
    if (*line == '\0') {
      if (parser_depth > 1 || limit < 0) {
        // Not a termination state, feed the line
        free(parser_line);
        miliReadLine("> ");
      } else
        break;
    } else if (*line == '`') {
      x = miliCons(makeRef((Ref)SYM_backquote, REF_SYMBOL), NIL);
      SHIFT(x);
      line++;
      miliParse(LIST(x), 1);
    } else if (*line == ',') {
      SHIFT(makeRef((Ref)SYM_comma, REF_SYMBOL));
      line++;
    } else if (*line == '\'') {
      x = miliCons(makeRef((Ref)SYM_quote, REF_SYMBOL), NIL);
      SHIFT(x);
      line++;
      miliParse(LIST(x), 1);
    } else if (*line == '.') {
      x = miliCons(NIL, NIL);
      line++;
      miliParse(LIST(x), 1);
      parent->cdr = CAR(x);
    } else if (*line == '(') {
      x = miliCons(NIL, NIL);
      SHIFT(x);
      line++;
      miliParse(LIST(x), -1);
    } else if (*line == ')') {
      --parser_depth;
      line++;
      miliPop(1);
      return 0;
    } else {
      if (strchr(numleads, *line))
        x = makeRef((Ref)strtoul(line, &line, 0), REF_ADDR);
      else {
        char *bgn = line;
        char *s;
        if (*line == '|') {
          int len = 0;
          for (line++; *line != '\0'; line++, len++)
            if (*line == '|' && *++line != '|')
              break;
          s = malloc(len * sizeof(char));
          s[len - 1] = '\0';
          for (char *p = s; bgn < line; *p++ = *bgn++)
            if (*bgn == '|')
              bgn++;
        } else {
          for (line++; *line != '\0' && !strchr(reschars, *line); line++)
            ;
          s = strndup(bgn, (int)(line - bgn));
        }
        x = miliIntern(s);
        free(s);
      }
      SHIFT(x);
    }
  }
  miliPop(1);
#undef x
  --parser_depth;
  return 0;
}

Ref miliPrintValue(Ref value);
Ref miliPrintList(Ref l) {
  if (!testMark(heapPos(l), MARK_00)) {
    setMark(LIST(l), MARK_00);
    miliPrintValue(CAR(l));
    if (LIST_P(CDR(l)) && !testMark(heapPos(CDR(l)), MARK_11))
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
    if (!testMark(heapPos(value), MARK_00)) {
      if (testMark(heapPos(value), MARK_11))
        printf("#%#lx=", heapPos(value));
      printf("("), miliPrintList(value), printf(")");
    } else
      printf("#%#lx#", heapPos(value));
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

INLINE Ref miliPrint(Ref value) {
  return markTree(value), miliPrintValue(value);
}

INLINE void miliPrimitive(char *name, Ref (*f)(Ref)) {
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
  symtbl[SYM_backquote] = "backquote";
  symtbl[SYM_quote] = "quote";
  symtbl[SYM_comma] = ",";
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
  miliPrimitive("quote", mili_quote);
  miliPrimitive("eval", mili_eval);
  miliPrimitive("cons", mili_cons);
  miliPrimitive("list", mili_list);
  miliPrimitive("car", mili_car);
  miliPrimitive("cdr", mili_cdr);
  miliPrimitive("equal", mili_equal);
  miliPrimitive("if", mili_if);
  miliPrimitive("atom", mili_atom);
  miliPrimitive("set", mili_set);
  miliPrimitive("define", mili_define);
  miliPrimitive("freeze", mili_freeze);
  miliPrimitive("+", mili_add);
  miliPrimitive("-", mili_sub);
  miliPrimitive("*", mili_mul);
  miliPrimitive("/", mili_div);
  /* A simple REPL */
  for (;;) {
    Node root = {NIL, NIL};
    miliReadLine("\n(mili) ");
    miliParse(&root, 1);
    miliPrint(miliEval(root.car));
    free(parser_line);
  }
  return 0;
}
