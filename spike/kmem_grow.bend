import Base

# The kernel's word storage (kernel.bend), grown by doubling: a flat array
# of 2^8 words at first, copied into one twice its size whenever more is
# needed, up to 2^maxd. The array alone travels with the kernel's state;
# the kernel keeps its capacity, from which the depth follows.

type M is Type:
  MG{a: Array<U32>}

# a new store and how many words it holds
def m_new(+maxd: Nat) -> M & U32:
  (MG{[0 : U32^8n]}, 256)

def m_get.fin(r: Array<U32> & U32) -> M & U32:
  (a, +v) = r
  (MG{a}, v)

def m_get(m: M, +i: U32) -> M & U32:
  match m:
    case MG{a}:
      m_get.fin(Array.get(U32, a, i))

def m_set(m: M, +i: U32, +v: U32) -> M:
  match m:
    case MG{a}:
      MG{Array.set(U32, a, i, v)}

type CP is Type:
  CP{src: Array<U32>, dst: Array<U32>}

def cp.step(r: Array<U32> & U32, dst: Array<U32>, +i: U32) -> CP:
  (src, +v) = r
  CP{src, Array.set(U32, dst, i, v)}

def copy(n: Nat, +i: U32, c: CP) -> Array<U32>:
  match n:
    case 0n:
      match c:
        case CP{src, dst}:
          dst
    case 1n+p:
      match c:
        case CP{src, dst}:
          copy(p, (i + 1 : U32), cp.step(Array.get(U32, src, i), dst, i))

# the depth of an array of cap words, cap a power of two
def depth(k: Nat, +cap: U32, +d: Nat) -> Nat:
  match k:
    case 0n:
      d
    case 1n+p:
      match cap:
        case 1:
          d
        case _:
          depth(p, (cap >> 1n : U32), 1n+d)

def grow(m: M, +cap: U32) -> M:
  match m:
    case MG{a}:
      MG{copy(U32.to_nat(cap), 0, CP{a, [0 : U32^Nat.add(depth(32n, cap, 0n), 1n)]})}

type Step is Type:
  GDone{m: M, +cap: U32}
  GMore{m: M, +cap: U32}

def decide(+fits: Bool, +full: Bool, m: M, +cap: U32) -> Step:
  match fits full:
    case True{} _:
      GDone{m, cap}
    case False{} True{}:
      GDone{m, cap}
    case False{} False{}:
      GMore{m, cap}

def ens(f: Nat, s: Step, +n: U32, +maxd: Nat) -> M & U32:
  match f:
    case 0n:
      match s:
        case GDone{m, +cap}:
          (m, cap)
        case GMore{m, +cap}:
          (m, cap)
    case 1n+p:
      match s:
        case GDone{m, +cap}:
          (m, cap)
        case GMore{m, +cap}:
          ens(p, decide(U32.is_le(n, (cap * 2 : U32)), Nat.is_ge(depth(32n, (cap * 2 : U32), 0n), maxd),
            grow(m, cap), (cap * 2 : U32)), n, maxd)

def m_ensure.go(fits: Bool, m: M, +n: U32, +cap: U32, +maxd: Nat) -> M & U32:
  match fits:
    case True{}:
      (m, cap)
    case False{}:
      ens(32n, decide(False{}, Nat.is_ge(depth(32n, cap, 0n), maxd), m, cap), n, maxd)

# room for words 0 .. n - 1 in a store of cap words, growing up to 2^maxd:
# the store and its capacity after, less than n if it could not grow
def m_ensure(m: M, +n: U32, +cap: U32, +maxd: Nat) -> M & U32:
  m_ensure.go(U32.is_le(n, cap), m, n, cap, maxd)

