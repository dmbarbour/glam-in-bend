import Base

# Reading a node's four words, as the kernel's rewrites do before each
# rewrite (spike/knet.bend's go): four reads, each a helper that carries
# the rewrite's context on (mode 0), against one read returning the four
# words together, the context carried once (mode 1). A table of 2^16
# nodes of four words; step i reads a node picked by i and the running
# sum, and feeds the sum back, so that nothing folds away.
#
#   node_read MODE STEPS

type S is Type:
  S{a: Array<U32>, +acc: U32}

def mix(+acc: U32, +w0: U32, +w1: U32, +w2: U32, +w3: U32) -> U32:
  ((((acc << 1n : U32) .^. w0 : U32) + (w1 .^. (w2 >> 3n : U32) : U32) : U32) .^. w3 : U32)

def ctx(+c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> U32:
  ((((c0 .^. c1 : U32) + (c2 .^. c3 : U32) : U32) .^. c4 : U32) + c5 : U32)

# the node step i reads, as a word index
def at(+i: U32, +acc: U32) -> U32:
  ((((i * 40503 : U32) + acc : U32) .&. 65535 : U32) << 2n : U32)

# Mode 0: a helper per read, each carrying the context

def m0.d(r: Array<U32> & U32, +acc: U32, +w0: U32, +w1: U32, +w2: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> S:
  (a, +w3) = r
  S{a, (mix(acc, w0, w1, w2, w3) + ctx(c0, c1, c2, c3, c4, c5) : U32)}

def m0.c(r: Array<U32> & U32, +acc: U32, +n: U32, +w0: U32, +w1: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> S:
  (a, +w2) = r
  m0.d(Array.get(U32, a, (n + 3 : U32)), acc, w0, w1, w2, c0, c1, c2, c3, c4, c5)

def m0.b(r: Array<U32> & U32, +acc: U32, +n: U32, +w0: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> S:
  (a, +w1) = r
  m0.c(Array.get(U32, a, (n + 2 : U32)), acc, n, w0, w1, c0, c1, c2, c3, c4, c5)

def m0.a(r: Array<U32> & U32, +acc: U32, +n: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> S:
  (a, +w0) = r
  m0.b(Array.get(U32, a, (n + 1 : U32)), acc, n, w0, c0, c1, c2, c3, c4, c5)

def m0(s: S, +i: U32) -> S:
  match s:
    case S{a, +acc}:
      m0.a(Array.get(U32, a, at(i, acc)), acc, at(i, acc), i, (i .^. acc : U32), (i + 7 : U32), (acc >> 2n : U32), (i * 3 : U32), (acc + 1 : U32))

# Mode 1: one read of four words, its chain carrying only what it read

type Q is Type:
  Q{a: Array<U32>, +w0: U32, +w1: U32, +w2: U32, +w3: U32}

def q.d(r: Array<U32> & U32, +w0: U32, +w1: U32, +w2: U32) -> Q:
  (a, +w3) = r
  Q{a, w0, w1, w2, w3}

def q.c(r: Array<U32> & U32, +n: U32, +w0: U32, +w1: U32) -> Q:
  (a, +w2) = r
  q.d(Array.get(U32, a, (n + 3 : U32)), w0, w1, w2)

def q.b(r: Array<U32> & U32, +n: U32, +w0: U32) -> Q:
  (a, +w1) = r
  q.c(Array.get(U32, a, (n + 2 : U32)), n, w0, w1)

def q.a(r: Array<U32> & U32, +n: U32) -> Q:
  (a, +w0) = r
  q.b(Array.get(U32, a, (n + 1 : U32)), n, w0)

def rd4(a: Array<U32>, +n: U32) -> Q:
  q.a(Array.get(U32, a, n), n)

def m1.fin(q: Q, +acc: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +c4: U32, +c5: U32) -> S:
  match q:
    case Q{a, +w0, +w1, +w2, +w3}:
      S{a, (mix(acc, w0, w1, w2, w3) + ctx(c0, c1, c2, c3, c4, c5) : U32)}

def m1(s: S, +i: U32) -> S:
  match s:
    case S{a, +acc}:
      m1.fin(rd4(a, at(i, acc)), acc, i, (i .^. acc : U32), (i + 7 : U32), (acc >> 2n : U32), (i * 3 : U32), (acc + 1 : U32))

def run0(k: Nat, s: S, +i: U32) -> S:
  match k:
    case 0n:
      s
    case 1n+p:
      run0(p, m0(s, i), (i + 1 : U32))

def run1(k: Nat, s: S, +i: U32) -> S:
  match k:
    case 0n:
      s
    case 1n+p:
      run1(p, m1(s, i), (i + 1 : U32))

# the table, word j a hash of j
def fill(k: Nat, a: Array<U32>, +j: U32) -> Array<U32>:
  match k:
    case 0n:
      a
    case 1n+p:
      fill(p, Array.set(U32, a, j, (j * 2654435761 : U32)), (j + 1 : U32))

def run(+mode: U32, k: Nat) -> S:
  match mode:
    case 0:
      run0(k, S{fill(262144n, [0 : U32^18n], 0), 0}, 0)
    case _:
      run1(k, S{fill(262144n, [0 : U32^18n], 0), 0}, 0)

def out(s: S) -> String:
  match s:
    case S{a, +acc}:
      U32.show(acc)

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{m, r2}:
          match r2:
            case Con{n, r3}:
              IO.print(out(run(Maybe.default(&2, U32, U32.read(m), 0), U32.to_nat(Maybe.default(&2, U32, U32.read(n), 1000)))))
            case Nil{}:
              IO.print("usage: node_read MODE STEPS")
        case Nil{}:
          IO.print("usage: node_read MODE STEPS")
    case Nil{}:
      IO.print("usage: node_read MODE STEPS")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
