# The store's growth as the laws see it (spike/GROW_LAWS.bend,
# cursor-laws.loop.shape.grow.copy.store): the array a store holds. No
# code calls it.

import Base
import ./kmem_grow.bend as KM

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
