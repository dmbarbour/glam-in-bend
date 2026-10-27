import Base

# The kernel's word storage (kernel.bend), preallocated: one flat array of
# 2^d words, made whole at the start.

type M is Type:
  MF{a: Array<U32>}

# a new store and how many words it holds
def m_new(+d: Nat) -> M & U32:
  (MF{[0 : U32^d]}, U32.from_nat(Nat.pow(2n, d)))

def m_get.fin(r: Array<U32> & U32) -> M & U32:
  (a, +v) = r
  (MF{a}, v)

def m_get(m: M, +i: U32) -> M & U32:
  match m:
    case MF{a}:
      m_get.fin(Array.get(U32, a, i))

def m_set(m: M, +i: U32, +v: U32) -> M:
  match m:
    case MF{a}:
      MF{Array.set(U32, a, i, v)}

# room for words 0 .. n - 1: the store and its capacity, which never grows
def m_ensure(m: M, +n: U32, +cap: U32, +maxd: Nat) -> M & U32:
  (m, cap)

