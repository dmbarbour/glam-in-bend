import Base

# The kernel's word storage (kernel.bend) as pages: 2^14 words a page, in a
# page table of up to 2^(maxd - 14) entries, a page made only when first
# needed. One page, the focus, is held out of the table; touching another
# swaps the focus back in and the other out, so accesses that stay in one
# page cost no more than a flat array's.

type M is Type:
  MP{pt: Array<Array<U32>>, cur: Array<U32>, +curp: U32, +np: U32, +maxp: U32}

def table(+d: Nat) -> Array<Array<U32>>:
  match d:
    case 0n:
      ALeaf{[0 : U32^0n]}
    case 1n+p:
      ANode{table(p), table(p)}

def m_new(+maxd: Nat) -> M:
  MP{table(Nat.sub(maxd, 14n)), [0 : U32^14n], 0, 1, U32.from_nat(Nat.pow(2n, Nat.sub(maxd, 14n)))}

def focus.take(r: Array<Array<U32>> & Array<U32>, +p: U32, +np: U32, +maxp: U32) -> M:
  (pt, pg) = r
  MP{pt, pg, p, np, maxp}

def focus.put(r: Array<Array<U32>> & Array<U32>, +p: U32, +np: U32, +maxp: U32) -> M:
  (pt, hole) = r
  focus.take(Array.swap(Array<U32>, pt, p, hole), p, np, maxp)

# make page p the focus
def focus(m: M, +p: U32) -> M:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      focus.put(Array.swap(Array<U32>, pt, curp, cur), p, np, maxp)

def m_get.fin(r: Array<U32> & U32, pt: Array<Array<U32>>, +curp: U32, +np: U32, +maxp: U32) -> M & U32:
  (cur, +v) = r
  (MP{pt, cur, curp, np, maxp}, v)

def m_get.cur(m: M, +off: U32) -> M & U32:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      m_get.fin(Array.get(U32, cur, off), pt, curp, np, maxp)

# the record taken apart once: a hit reads the focus directly
def m_get.go(same: Bool, pt: Array<Array<U32>>, cur: Array<U32>, +curp: U32, +np: U32, +maxp: U32, +p: U32, +off: U32) -> M & U32:
  match same:
    case True{}:
      m_get.fin(Array.get(U32, cur, off), pt, curp, np, maxp)
    case False{}:
      m_get.cur(focus(MP{pt, cur, curp, np, maxp}, p), off)

def m_get(m: M, +i: U32) -> M & U32:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      m_get.go(U32.is_eq((i >> 14n : U32), curp), pt, cur, curp, np, maxp, (i >> 14n : U32), (i .&. 16383 : U32))

def m_set.cur(m: M, +off: U32, +v: U32) -> M:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      MP{pt, Array.set(U32, cur, off, v), curp, np, maxp}

def m_set.go(same: Bool, pt: Array<Array<U32>>, cur: Array<U32>, +curp: U32, +np: U32, +maxp: U32, +p: U32, +off: U32, +v: U32) -> M:
  match same:
    case True{}:
      MP{pt, Array.set(U32, cur, off, v), curp, np, maxp}
    case False{}:
      m_set.cur(focus(MP{pt, cur, curp, np, maxp}, p), off, v)

def m_set(m: M, +i: U32, +v: U32) -> M:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      m_set.go(U32.is_eq((i >> 14n : U32), curp), pt, cur, curp, np, maxp, (i >> 14n : U32), (i .&. 16383 : U32), v)

type PStep is Type:
  PDone{m: M, +ok: Bool}
  PMore{m: M}

def pdecide.go(+fits: Bool, +full: Bool, m: M) -> PStep:
  match fits full:
    case True{} _:
      PDone{m, True{}}
    case False{} True{}:
      PDone{m, False{}}
    case False{} False{}:
      PMore{m}

def pdecide(m: M, +n: U32) -> PStep:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      pdecide.go(U32.is_le(n, (np << 14n : U32)), U32.is_ge(np, maxp), MP{pt, cur, curp, np, maxp})

def addpage(m: M) -> M:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      MP{Array.set(Array<U32>, pt, np, [0 : U32^14n]), cur, curp, (np + 1 : U32), maxp}

def pens(f: Nat, s: PStep, +n: U32) -> M & Bool:
  match f:
    case 0n:
      match s:
        case PDone{m, +ok}:
          (m, ok)
        case PMore{m}:
          (m, False{})
    case 1n+p:
      match s:
        case PDone{m, +ok}:
          (m, ok)
        case PMore{m}:
          pens(p, pdecide(addpage(m), n), n)

# room for words 0 .. n - 1, or false
def m_ensure(m: M, +n: U32) -> M & Bool:
  pens(64n, pdecide(m, n), n)

# how many words fit now
def m_cap(m: M) -> M & U32:
  match m:
    case MP{pt, cur, +curp, +np, +maxp}:
      (MP{pt, cur, curp, np, maxp}, (np << 14n : U32))
