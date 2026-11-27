# The store's growth as the laws see it (spike/GROW_LAWS.bend,
# cursor-laws.loop.shape.grow.copy.store): the array a store holds. No
# code calls it.

import Base
import ./kmem_grow.bend as KM
import ./kprim.bend as P
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

def arr(m: KM.M) -> Array<U32>:
  match m:
    case KM.MG{a}:
      a

# the fresh nodes growth threads, nodes i to i + k - 1 as their
# references (four words a node), in the free list's order
def fresh(k: Nat, +i: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{(i << 2n : U32), fresh(p, (i + 1 : U32))}

# every one of ys at or past word 2^d, as growth's fresh nodes lie past
# the old store
def above(ys: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+n, t}:
      Nat.is_le(Nat.pow(2n, d), U32.to_nat(n)) && above(t, d)

# The heap's shape (cursor-laws.loop.shape.grow.copy.store.shape): its
# store full at 2^(e + 2) words, its capacity word reading wc = 2^e
# nodes, 3 <= e <= 28 (512 words at first, up to 2^30, P.w_maxd); word 3
# read through the pair Array.get hands back, the store linear
def shape.go(r: Array<U32> & U32, +e: Nat) -> Bool:
  (w, +x) = r
  AD.full(U32, w, 2n+e) && (Nat.is_eq(U32.to_nat(x), Nat.pow(2n, e)) && (Nat.is_le(3n, e) && Nat.is_le(e, 28n)))

def shape(w: Array<U32>, +e: Nat) -> Bool:
  shape.go(Array.get(U32, w, P.at_wcap()), e)
