import Base

# The kernel's word storage (kernel.bend), grown by doubling: a flat array
# of 2^8 words at first, copied into one twice its size whenever more is
# needed, up to 2^maxd.

type M is Type:
  MG{a: Array<U32>, +d: Nat, +cap: U32, +maxd: Nat}

def m_new(+maxd: Nat) -> M:
  MG{[0 : U32^8n], 8n, 256, maxd}

def m_get.fin(r: Array<U32> & U32, +d: Nat, +cap: U32, +maxd: Nat) -> M & U32:
  (a, +v) = r
  (MG{a, d, cap, maxd}, v)

def m_get(m: M, +i: U32) -> M & U32:
  match m:
    case MG{a, +d, +cap, +maxd}:
      m_get.fin(Array.get(U32, a, i), d, cap, maxd)

def m_set(m: M, +i: U32, +v: U32) -> M:
  match m:
    case MG{a, +d, +cap, +maxd}:
      MG{Array.set(U32, a, i, v), d, cap, maxd}

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

def grow(m: M) -> M:
  match m:
    case MG{a, +d, +cap, +maxd}:
      MG{copy(U32.to_nat(cap), 0, CP{a, [0 : U32^Nat.add(d, 1n)]}), Nat.add(d, 1n), (cap * 2 : U32), maxd}

type Step is Type:
  GDone{m: M, +ok: Bool}
  GMore{m: M}

def decide.go(+fits: Bool, +full: Bool, m: M) -> Step:
  match fits full:
    case True{} _:
      GDone{m, True{}}
    case False{} True{}:
      GDone{m, False{}}
    case False{} False{}:
      GMore{m}

def decide(m: M, +n: U32) -> Step:
  match m:
    case MG{a, +d, +cap, +maxd}:
      decide.go(U32.is_le(n, cap), Nat.is_ge(d, maxd), MG{a, d, cap, maxd})

def ens(f: Nat, s: Step, +n: U32) -> M & Bool:
  match f:
    case 0n:
      match s:
        case GDone{m, +ok}:
          (m, ok)
        case GMore{m}:
          (m, False{})
    case 1n+p:
      match s:
        case GDone{m, +ok}:
          (m, ok)
        case GMore{m}:
          ens(p, decide(grow(m), n), n)

# room for words 0 .. n - 1, or false
def m_ensure(m: M, +n: U32) -> M & Bool:
  ens(32n, decide(m, n), n)
