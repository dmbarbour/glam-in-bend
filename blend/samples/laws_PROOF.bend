# Written by Blend from laws.blend; do not edit.
import Base
import ./laws.bend as Blend_0
import ./laws_LAWS.bend as Blend_Laws

# blend: laws.blend:30
def Blend_Laws.NatAdd.right_id(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Blend_Laws.NatAdd.right_id(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws.blend:21
def Blend_Laws.NatAdd.double_op(x):
  {==}

# blend: laws.blend:46
def Blend_Laws.AnyOf.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:52
def Blend_Laws.AnyOf.double_op(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}
