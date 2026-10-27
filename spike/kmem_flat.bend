import Base

# The kernel's word storage (kernel.bend), preallocated: one flat array of
# 2^d words, made whole at the start.

type M is Type:
  MF{a: Array<U32>, +cap: U32}

def m_new(+d: Nat) -> M:
  MF{[0 : U32^d], U32.from_nat(Nat.pow(2n, d))}

def m_get.fin(r: Array<U32> & U32, +cap: U32) -> M & U32:
  (a, +v) = r
  (MF{a, cap}, v)

def m_get(m: M, +i: U32) -> M & U32:
  match m:
    case MF{a, +cap}:
      m_get.fin(Array.get(U32, a, i), cap)

def m_set(m: M, +i: U32, +v: U32) -> M:
  match m:
    case MF{a, +cap}:
      MF{Array.set(U32, a, i, v), cap}

# room for words 0 .. n - 1, or false
def m_ensure(m: M, +n: U32) -> M & Bool:
  match m:
    case MF{a, +cap}:
      (MF{a, cap}, U32.is_le(n, cap))
