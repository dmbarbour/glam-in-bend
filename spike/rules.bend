import Base

# The interaction rules, as data. A redex pairs a node whose principal
# port is negative (A) with one whose principal is positive (B). A rule
# says which nodes replace them and how the new ports, and the four
# external peers of A's and B's auxiliary ports, are linked. The reducer
# interprets rules; laws check every rule is polarized and linear.

# Node kinds and port polarity
# ============================

# Ports, by kind: polarity of ports 0 (principal), 1, 2.
#   Fn    function bind     [+ fn,    - result, + arg]
#   Ap    application bind  [- ap,    - arg,    + result]
#   Copy  copy fan          [- input, + left,   + right]
#   Merge merge fan         [+ out,   - left,   - right]
#   Data  value             [+]
#   EraN  eraser, consuming [-]
#   EraP  eraser, providing [+]   (an error value, as void)
#   Root  the net's consumer [-]
type NodeKind is Data:
  KFree{}
  KFn{}
  KAp{}
  KCopy{}
  KMerge{}
  KData{}
  KEraN{}
  KEraP{}
  KRoot{}

type Pol is Data:
  Pos{}
  Neg{}

def flip(p: Pol) -> Pol:
  match p:
    case Pos{}:
      Neg{}
    case Neg{}:
      Pos{}

def pol_eq(a: Pol, b: Pol) -> Bool:
  match a b:
    case Pos{} Pos{}:
      True{}
    case Neg{} Neg{}:
      True{}
    case _ _:
      False{}

def arity(k: NodeKind) -> Nat:
  match k:
    case KFn{}:
      3n
    case KAp{}:
      3n
    case KCopy{}:
      3n
    case KMerge{}:
      3n
    case KFree{}:
      0n
    case _:
      1n

# the polarity of port p of a node of kind k; ports past its arity are
# never asked for, and answer Pos
def port_pol(k: NodeKind, p: Nat) -> Pol:
  match k p:
    case KFn{} 1n:
      Neg{}
    case KAp{} 0n:
      Neg{}
    case KAp{} 1n:
      Neg{}
    case KCopy{} 0n:
      Neg{}
    case KMerge{} 1n:
      Neg{}
    case KMerge{} 2n:
      Neg{}
    case KEraN{} 0n:
      Neg{}
    case KRoot{} 0n:
      Neg{}
    case _ _:
      Pos{}

# Rules
# =====

# an end of a new link: Ext i is the peer of an auxiliary port of the
# redex (0 and 1: A's ports 1 and 2; 2 and 3: B's), New j p is port p of
# the rule's j-th new node
type End is Data:
  Ext{i: Nat}
  New{j: Nat, p: Nat}

type Link is Data:
  Link{a: End, b: End}

# where a new node's payload comes from: nothing; B's payload (data);
# A's or B's fan identity, as is or extended with the other fan's
# identity and a branch (a fan commuting through a fan)
type Src is Data:
  SNone{}
  SPayB{}
  SFanA{}
  SFanB{}
  SFanAx{branch: Nat}
  SFanBx{branch: Nat}

type Spec is Data:
  Spec{k: NodeKind, src: Src}

type Rule is Data:
  RWire{nodes: List<&2, Spec>, links: List<&2, Link>}
  RCall{}
  RStuck{}

def lk(a: End, b: End) -> Link:
  Link{a, b}

def nw(j: Nat, p: Nat) -> End:
  New{j, p}

def ex(i: Nat) -> End:
  Ext{i}

# a copy meets a merge: residuals of one duplication annihilate; others
# commute, each fan copied onto the other's auxiliary side
def rule.fans(same: Bool) -> Rule:
  match same:
    case True{}:
      RWire{[], [lk(ex(0n), ex(2n)), lk(ex(1n), ex(3n))]}
    case False{}:
      RWire{[Spec{KMerge{}, SFanBx{0n}}, Spec{KMerge{}, SFanBx{1n}}, Spec{KCopy{}, SFanAx{0n}}, Spec{KCopy{}, SFanAx{1n}}],
        [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n)), lk(nw(2n, 0n), ex(2n)), lk(nw(3n, 0n), ex(3n)),
         lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n)), lk(nw(3n, 1n), nw(0n, 2n)), lk(nw(3n, 2n), nw(1n, 2n))]}

# A, negative principal, meets B, positive principal
def rule.ap(b: NodeKind) -> Rule:
  match b:
    # beta: the bind's auxiliaries join crossed
    case KFn{}:
      RWire{[], [lk(ex(0n), ex(3n)), lk(ex(1n), ex(2n))]}
    # applying a superposition: the application is copied onto each side
    case KMerge{}:
      RWire{[Spec{KAp{}, SNone{}}, Spec{KAp{}, SNone{}}, Spec{KCopy{}, SFanB{}}, Spec{KMerge{}, SFanB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(3n)),
         lk(nw(2n, 0n), ex(0n)), lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n)),
         lk(nw(3n, 0n), ex(1n)), lk(nw(3n, 1n), nw(0n, 2n)), lk(nw(3n, 2n), nw(1n, 2n))]}
    case KData{}:
      RCall{}
    # applying an error value: drop the argument, the result is an error
    case KEraP{}:
      RWire{[Spec{KEraN{}, SNone{}}, Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n))]}
    case _:
      RStuck{}

def rule.copy(b: NodeKind, same: Bool) -> Rule:
  match b:
    # duplicating a function: two functions, a copy of the body's result,
    # a merge of the argument's uses
    case KFn{}:
      RWire{[Spec{KFn{}, SNone{}}, Spec{KFn{}, SNone{}}, Spec{KCopy{}, SFanA{}}, Spec{KMerge{}, SFanA{}}],
        [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n)),
         lk(ex(2n), nw(2n, 0n)), lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n)),
         lk(ex(3n), nw(3n, 0n)), lk(nw(3n, 1n), nw(0n, 2n)), lk(nw(3n, 2n), nw(1n, 2n))]}
    case KMerge{}:
      rule.fans(same)
    # duplicating data shares it
    case KData{}:
      RWire{[Spec{KData{}, SPayB{}}, Spec{KData{}, SPayB{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n))]}
    case KEraP{}:
      RWire{[Spec{KEraP{}, SNone{}}, Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n))]}
    case _:
      RStuck{}

def rule.era(b: NodeKind) -> Rule:
  match b:
    # erasing a function: its body's result is dropped, its argument's
    # uses get an error value
    case KFn{}:
      RWire{[Spec{KEraN{}, SNone{}}, Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(3n))]}
    case KMerge{}:
      RWire{[Spec{KEraN{}, SNone{}}, Spec{KEraN{}, SNone{}}], [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(3n))]}
    case KData{}:
      RWire{[], []}
    case KEraP{}:
      RWire{[], []}
    case _:
      RStuck{}

# the rule for A meeting B, A's principal negative; same says whether two
# fans are residuals of one duplication
def rule(a: NodeKind, b: NodeKind, same: Bool) -> Rule:
  match a:
    case KAp{}:
      rule.ap(b)
    case KCopy{}:
      rule.copy(b, same)
    case KEraN{}:
      rule.era(b)
    case _:
      RStuck{}

# Checks, the laws' subject
# =========================

def nat_eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 1n+x 1n+y:
      nat_eq(x, y)
    case _ _:
      False{}

def end_eq(a: End, b: End) -> Bool:
  match a b:
    case Ext{i} Ext{j}:
      nat_eq(i, j)
    case New{i, p} New{j, q}:
      nat_eq(i, j) && nat_eq(p, q)
    case _ _:
      False{}

def spec_kind(xs: List<&2, Spec>, j: Nat) -> NodeKind:
  match xs j:
    case Nil{} _:
      KFree{}
    case Con{Spec{k, s}, t} 0n:
      k
    case Con{h, t} 1n+i:
      spec_kind(t, i)

# the polarity of an end: an external peer's is the opposite of the
# auxiliary port it was linked to
def end_pol(+a: NodeKind, +b: NodeKind, +xs: List<&2, Spec>, e: End) -> Pol:
  match e:
    case Ext{i}:
      match i:
        case 0n:
          flip(port_pol(a, 1n))
        case 1n:
          flip(port_pol(a, 2n))
        case 2n:
          flip(port_pol(b, 1n))
        case _:
          flip(port_pol(b, 2n))
    case New{j, p}:
      port_pol(spec_kind(xs, j), p)

def links_polarized(+a: NodeKind, +b: NodeKind, +xs: List<&2, Spec>, ls: List<&2, Link>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{Link{x, y}, t}:
      Bool.not(pol_eq(end_pol(a, b, xs, x), end_pol(a, b, xs, y))) && links_polarized(a, b, xs, t)

# every link of the rule joins a positive port to a negative one
def polarized(+a: NodeKind, +b: NodeKind, r: Rule) -> Bool:
  match r:
    case RWire{xs, ls}:
      links_polarized(a, b, xs, ls)
    case _:
      True{}

def one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def uses(ls: List<&2, Link>, +e: End) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{Link{x, y}, t}:
      Nat.add(Nat.add(one_if(end_eq(x, e)), one_if(end_eq(y, e))), uses(t, e))

# the ends a rule must link: A's and B's auxiliary peers, then every port
# of every new node
def aux_ends(n: Nat, +base: Nat) -> List<&2, End>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Ext{base} <> aux_ends(p, 1n+base)

def node_ends(+j: Nat, n: Nat, +p: Nat) -> List<&2, End>:
  match n:
    case 0n:
      Nil{}
    case 1n+q:
      New{j, p} <> node_ends(j, q, 1n+p)

def new_ends(xs: List<&2, Spec>, +j: Nat) -> List<&2, End>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Spec{k, s}, t}:
      List.append(&2, End, node_ends(j, arity(k), 0n), new_ends(t, 1n+j))

def expected(+a: NodeKind, +b: NodeKind, +xs: List<&2, Spec>) -> List<&2, End>:
  List.append(&2, End, aux_ends(Nat.sub(arity(a), 1n), 0n),
    List.append(&2, End, aux_ends(Nat.sub(arity(b), 1n), 2n), new_ends(xs, 0n)))

def all_once(+ls: List<&2, Link>, es: List<&2, End>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      nat_eq(uses(ls, e), 1n) && all_once(ls, t)

def ends_count(ls: List<&2, Link>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{l, t}:
      2n+ends_count(t)

# every end the rule must link is linked exactly once, and nothing else
def linear(+a: NodeKind, +b: NodeKind, r: Rule) -> Bool:
  match r:
    case RWire{+xs, +ls}:
      all_once(ls, expected(a, b, xs)) && nat_eq(ends_count(ls), List.length(&2, End, expected(a, b, xs)))
    case _:
      True{}
