# Written by Blend from laws.blend; do not edit.
import Base
import ./laws.bend as Blend_0
import ./laws_LAWS.bend as Blend_Laws

# blend: laws.blend:33
def Blend_Laws.NatAdd.right_id(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Blend_Laws.NatAdd.right_id(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws.blend:40
def NatAdd.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# blend: laws.blend:51
def Blend_Laws.NatAdd.op_succ(a, b):
  NatAdd.add_succ(a, b)

# blend: laws.blend:24
def Blend_Laws.NatAdd.double_op(x):
  {==}

# blend: laws.blend:62
def Blend_Laws.AnyOf.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:68
def Blend_Laws.AnyOf.double_op(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:80
def Blend_Laws.double_three():
  {==}
