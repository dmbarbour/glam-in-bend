# The store's growth as the laws see it (spike/GROW_LAWS.bend,
# cursor-laws.loop.shape.grow.copy.store): the array a store holds. No
# code calls it.

import Base
import ./kmem_grow.bend as KM

def arr(m: KM.M) -> Array<U32>:
  match m:
    case KM.MG{a}:
      a
