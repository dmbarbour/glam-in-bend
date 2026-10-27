# The evaluator spike's proofs.

import Base
import ./LAWS.bend as Laws
import ./store.bend as S

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# by cases on the free list, then the fresh count: each moves one slot to
# live, and add_succ shifts the 1 across
def Laws.alloc_conserves(m):
  match m:
    case S.Meta{free, fresh, live}:
      match free:
        case Con{s, rest}:
          %add_succ(live, Nat.add(S.len(rest), fresh)) : {1n+Nat.add(live, Nat.add(S.len(rest), fresh)) == _ : Nat}
          {==}
        case Nil{}:
          match fresh:
            case 0n:
              {==}
            case 1n+p:
              %add_succ(live, p) : {1n+Nat.add(live, p) == _ : Nat}
              {==}

def Laws.free_conserves(m, s):
  match m:
    case S.Meta{free, fresh, live}:
      match live:
        case 0n:
          {==}
        case 1n+q:
          %add_succ(q, Nat.add(S.len(free), fresh)) : {_ == 1n+Nat.add(q, Nat.add(S.len(free), fresh)) : Nat}
          {==}
