import Base

# Control runs, a simplified model for laws (pairing-fusion in
# docs/plans/NetPairing_2026-10-26.md). Levels and indices are Nat. A
# control that raises levels above n by b (kprim.bend's lift, up) stands
# for a run of unit brackets at n, n + 1, ..., n + b - 1, crossed in that
# order: what fusion makes (V.compose) and peeling takes apart. Facing
# units of one index cancel; at different indices, the higher index moves
# through the lower unit.

# j > n
def above(j: Nat, n: Nat) -> Bool:
  match j n:
    case 0n _:
      False{}
    case 1n+a 0n:
      True{}
    case 1n+a 1n+m:
      above(a, m)

def raise.go(a: Bool, +j: Nat, +b: Nat) -> Nat:
  match a:
    case True{}:
      Nat.add(j, b)
    case False{}:
      j

# a level j through a run raising levels above n by b
def raise(+n: Nat, +b: Nat, +j: Nat) -> Nat:
  raise.go(above(j, n), j, b)

# j through unit brackets at n, n + 1, ..., n + b - 1, in that order
def units(b: Nat, +n: Nat, +j: Nat) -> Nat:
  match b:
    case 0n:
      j
    case 1n+p:
      units(p, 1n+n, raise(n, 1n, j))

# Facing runs of one index: a LiftC run (n, c) above a Lift run (n, l).
# Their inner units meet first and cancel, one pair at a time; what is
# left of the longer run stays. The result: 0 for nothing, 1 a Lift run,
# 2 a LiftC run, with its index and length.
type Left is Data:
  Left{+side: U32, +n: Nat, +len: Nat}

def pair_off(c: Nat, l: Nat, +n: Nat) -> Left:
  match c l:
    case 0n 0n:
      Left{0, n, 0n}
    case 0n 1n+q:
      Left{1, n, 1n+q}
    case 1n+p 0n:
      Left{2, n, 1n+p}
    case 1n+p 1n+q:
      pair_off(p, q, 1n+n)

# peeling (net.bend, kprim.bend): the longer run keeps as many units as
# the other has, which cancel with it, and the rest stays from the index
# where they end
def peel.go(+lt: Bool, +eq: Bool, +n: Nat, +c: Nat, +l: Nat) -> Left:
  match lt eq:
    case _ True{}:
      Left{0, Nat.add(c, n), 0n}
    case True{} False{}:
      Left{1, Nat.add(c, n), Nat.sub(l, c)}
    case False{} False{}:
      Left{2, Nat.add(l, n), Nat.sub(c, l)}

def peel(+n: Nat, +c: Nat, +l: Nat) -> Left:
  peel.go(Nat.is_lt(c, l), Nat.is_eq(c, l), n, c, l)
