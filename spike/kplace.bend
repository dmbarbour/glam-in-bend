import Base
import ./rules.bend as R
import ./freelist.bend as FL
import ./wiring.bend as W

# The kernel's placement of a rewrite's new nodes, joining the free-list
# model (freelist.bend) and the wiring model (wiring.bend), for laws
# (`heap-strategies.net.wiring.alloc` in docs/plans/HeapModel_2026-10-27.md):
# the first two new nodes take the pair's own slots, the rest the free
# list's heads (kprim.bend's renode and alloc); a rule making one node
# frees b, one making none frees b, then a (fresh2). in_step says the two
# models agree on which slots are free.

def same_b(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# slot by slot, free in the one exactly when its kind is free in the other
def in_step(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>) -> Bool:
  match s ks:
    case Nil{} Nil{}:
      True{}
    case Con{x, t} Con{k, u}:
      same_b(FL.is_free(x), W.is_free_kind(k)) && in_step(t, u)
    case _ _:
      False{}

def ghost(f: FL.FL) -> List<&2, Nat>:
  match f:
    case FL.FL{s, fh, l}:
      l

def slots_of(f: FL.FL) -> List<&2, FL.Slot>:
  match f:
    case FL.FL{s, fh, l}:
      s

# the slots n allocations take, the head's each time; fewer when the list
# runs out, where the kernel grows its storage first
def allocs(n: Nat, f: FL.FL) -> List<&2, Nat>:
  match n f:
    case 0n _:
      Nil{}
    case 1n+m FL.FL{+s, fh, +l}:
      match fh:
        case 0n:
          Nil{}
        case 1n++i:
          i <> allocs(m, FL.alloc(FL.FL{s, 1n+i, l}))

def after(n: Nat, f: FL.FL) -> FL.FL:
  match n:
    case 0n:
      f
    case 1n+m:
      after(m, FL.alloc(f))

# where a rewrite making k nodes puts them
def kslots(+a: Nat, +b: Nat, k: Nat, f: FL.FL) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n:
      [a]
    case 2n+m:
      a <> (b <> allocs(m, f))

# the free list after
def kfree(+a: Nat, +b: Nat, k: Nat, f: FL.FL) -> FL.FL:
  match k:
    case 0n:
      FL.free(FL.free(f, b), a)
    case 1n:
      FL.free(f, b)
    case 2n+m:
      after(m, f)

# the free list holds at least n
def has(n: Nat, l: List<&2, Nat>) -> Bool:
  match n l:
    case 0n _:
      True{}
    case 1n+m Nil{}:
      False{}
    case 1n+m Con{j, t}:
      has(m, t)

# the kernel's slots meet rewrite_placed_wired's conditions: no slot
# twice, each the pair's own or free, one for each of the k new nodes
def kslots_ok(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +k: Nat, +f: FL.FL) -> Bool:
  W.nodup_nat(kslots(a, b, k, f)) && (W.slots_ok(ks, a, b, kslots(a, b, k, f)) && R.nat_eq(List.length(&2, Nat, kslots(a, b, k, f)), k))

# no kind of ks is free: a rule's new nodes' kinds
def kinds_live(ks: List<&2, R.NodeKind>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{k, t}:
      Bool.not(W.is_free_kind(k)) && kinds_live(t)

# a rule's new nodes' kinds are live; a stuck pair makes none
def rule_live(r: R.Rule) -> Bool:
  match r:
    case R.RWire{xs, ls}:
      kinds_live(W.kinds(xs))
    case R.RStuck{}:
      True{}

# A step of the rule table at the kernel's placement: the free list
# holding enough for the rule's new nodes, the kinds after, the free list
# after; a stuck pair changes nothing.

def step_has(r: R.Rule, l: List<&2, Nat>) -> Bool:
  match r:
    case R.RWire{xs, ls}:
      has(Nat.sub(List.length(&2, R.Spec, xs), 2n), l)
    case R.RStuck{}:
      True{}

def step_kinds(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, r: R.Rule, f: FL.FL) -> List<&2, R.NodeKind>:
  match r:
    case R.RWire{+xs, ls}:
      W.rp_kinds(ks, a, b, kslots(a, b, List.length(&2, R.Spec, xs), f), xs)
    case R.RStuck{}:
      ks

def step_free(+a: Nat, +b: Nat, r: R.Rule, f: FL.FL) -> FL.FL:
  match r:
    case R.RWire{xs, ls}:
      kfree(a, b, List.length(&2, R.Spec, xs), f)
    case R.RStuck{}:
      f

# Growth
# ======
#
# When its free list runs out, the kernel doubles its storage and threads
# the new nodes onto the list in order, their headers zero, so free
# (kprim.bend's grow.done and thread). grow appends n free slots, each
# linking the next, the last the old head, the first now the head; the
# kinds grow by as many free nodes. The kernel grows only with the list
# empty, the old head none, and takes the first new slot at once.

# the head after n new slots from slot i: the first, or the old head x if
# none
def ghead(+i: Nat, n: Nat, x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      1n+i

# n free slots from slot i, each linking the next, the last x
def threaded(n: Nat, +i: Nat, +x: Nat) -> List<&2, FL.Slot>:
  match n:
    case 0n:
      Nil{}
    case 1n++m:
      FL.Free{ghead(1n+i, m, x)} <> threaded(m, 1n+i, x)

def grow(f: FL.FL, +n: Nat) -> FL.FL:
  match f:
    case FL.FL{+s, +fh, l}:
      FL.FL{List.append(&2, FL.Slot, s, threaded(n, List.length(&2, FL.Slot, s), fh)), ghead(List.length(&2, FL.Slot, s), n, fh),
        List.append(&2, Nat, W.range(n, List.length(&2, FL.Slot, s)), l)}

def frees(n: Nat) -> List<&2, R.NodeKind>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      R.KFree{} <> frees(m)

def grow_kinds(ks: List<&2, R.NodeKind>, n: Nat) -> List<&2, R.NodeKind>:
  List.append(&2, R.NodeKind, ks, frees(n))

def main() -> FL.FL:
  grow(FL.FL{[FL.Used{}, FL.Free{0n}], 2n, [1n]}, 3n)
