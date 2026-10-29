import Base

# The net's free list as a model in Nat, for laws
# (`heap-strategies.net.freelist.law` in docs/plans/HeapModel_2026-10-27.md):
# slots as the kernel keeps nodes, a free one linking the next free slot as
# a free node's word 1 does (kprim.bend's free and alloc), the head beside
# them, and the list itself, which the model keeps as its own record of
# what the links should spell. ok says the links from the head spell that
# list, which holds every free slot and no slot twice: each free slot is
# on the free list exactly once, and nothing else is. The laws
# free_list_alloc and free_list_free say both operations keep it.

# a slot in use, or free, linking the next free slot (its index plus one,
# 0 for none)
type Slot is Data:
  Used{}
  Free{next: Nat}

# the slots, the head (an index plus one, 0 for none) and the list
type FL is Data:
  FL{s: List<&2, Slot>, fh: Nat, l: List<&2, Nat>}

def same(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 1n+x 1n+y:
      same(x, y)
    case _ _:
      False{}

def is_free(c: Slot) -> Bool:
  match c:
    case Used{}:
      False{}
    case Free{n}:
      True{}

def next_of(c: Slot) -> Nat:
  match c:
    case Used{}:
      0n
    case Free{n}:
      n

# slot i, in use past the end
def get(s: List<&2, Slot>, i: Nat) -> Slot:
  match s i:
    case Nil{} _:
      Used{}
    case Con{c, t} 0n:
      c
    case Con{c, t} 1n+j:
      get(t, j)

# slot i replaced by v, nothing past the end
def set(s: List<&2, Slot>, i: Nat, v: Slot) -> List<&2, Slot>:
  match s i:
    case Nil{} _:
      Nil{}
    case Con{c, t} 0n:
      Con{v, t}
    case Con{c, t} 1n+j:
      Con{c, set(t, j, v)}

# slot i exists and is in use
def in_use(s: List<&2, Slot>, i: Nat) -> Bool:
  match s i:
    case Nil{} _:
      False{}
    case Con{c, t} 0n:
      Bool.not(is_free(c))
    case Con{c, t} 1n+j:
      in_use(t, j)

def mem(+i: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{j, t}:
      same(i, j) || mem(i, t)

def nodup(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{+j, +t}:
      Bool.not(mem(j, t)) && nodup(t)

# the links from x spell l: each slot on it free, linking the next
def walks(l: List<&2, Nat>, +s: List<&2, Slot>, x: Nat) -> Bool:
  match l:
    case Nil{}:
      same(x, 0n)
    case Con{+j, t}:
      same(x, 1n+j) && (is_free(get(s, j)) && walks(t, s, next_of(get(s, j))))

# every free slot below n is on l
def listed(+s: List<&2, Slot>, n: Nat, +l: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n++k:
      (Bool.not(is_free(get(s, k))) || mem(k, l)) && listed(s, k, l)

def ok(f: FL) -> Bool:
  match f:
    case FL{+s, fh, +l}:
      walks(l, s, fh) && (nodup(l) && listed(s, List.length(&2, Slot, s), l))

def rest(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case Con{j, t}:
      t

def alloc.go(c: Slot, s: List<&2, Slot>, +i: Nat, l: List<&2, Nat>) -> FL:
  match c:
    case Used{}:
      FL{s, 1n+i, l}
    case Free{n}:
      FL{set(s, i, Used{}), n, rest(l)}

# take the head's slot, if the list has one, and put it in use; the slot
# taken is the head's index (free_list_takes_free)
def alloc(f: FL) -> FL:
  match f:
    case FL{+s, fh, l}:
      match fh:
        case 0n:
          FL{s, 0n, l}
        case 1n++i:
          alloc.go(get(s, i), s, i, l)

# slot i, in use, freed to the head of the list
def free(f: FL, +i: Nat) -> FL:
  match f:
    case FL{s, fh, l}:
      FL{set(s, i, Free{fh}), 1n+i, Con{i, l}}

def main() -> Bool:
  ok(alloc(free(FL{[Used{}, Used{}, Free{0n}], 3n, [2n]}, 0n)))
