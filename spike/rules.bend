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
#   Call  strict call       [- arg,   + result]  (a builtin awaiting data)
#   Lift  level control     [- in,    + out]     facing the source
#   LiftC level control     [+ out,   - in]      facing the consumer
#         (a bracket or croissant: a node meeting its principal crosses
#         to the other side with its level adjusted)
#   CopyL, CopyR   linear copy  [- input, + the output kept]
#   MergeL, MergeR linear merge [+ out,   - the input kept]
#         (a fan one side of which was erased, named for the side it
#         keeps: Linear fans, below)
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
  KCall{}
  KLift{}
  KLiftC{}
  KCopyL{}
  KCopyR{}
  KMergeL{}
  KMergeR{}

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
    case KCall{}:
      2n
    case KLift{}:
      2n
    case KLiftC{}:
      2n
    case KCopyL{}:
      2n
    case KCopyR{}:
      2n
    case KMergeL{}:
      2n
    case KMergeR{}:
      2n
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
    case KCall{} 0n:
      Neg{}
    case KLift{} 0n:
      Neg{}
    case KLiftC{} 1n:
      Neg{}
    case KCopyL{} 0n:
      Neg{}
    case KCopyR{} 0n:
      Neg{}
    case KMergeL{} 1n:
      Neg{}
    case KMergeR{} 1n:
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

# where a new node's payload comes from: nothing; A's or B's payload
# (data, a call's function, a control node); A's function applied to B's
# data; A's or B's fan identity; A's or B's payload (a level, a fan's, a
# control's index) passed through the other, a control node
type Src is Data:
  SNone{}
  SPayA{}
  SPayB{}
  SApply{}
  SFanA{}
  SFanB{}
  SLiftA{}
  SLiftB{}

type Spec is Data:
  Spec{k: NodeKind, src: Src}

type Rule is Data:
  RWire{nodes: List<&2, Spec>, links: List<&2, Link>}
  RStuck{}

def lk(a: End, b: End) -> Link:
  Link{a, b}

def nw(j: Nat, p: Nat) -> End:
  New{j, p}

def ex(i: Nat) -> End:
  Ext{i}

# a copy meets a merge: residuals of one duplication annihilate; others
# commute, each fan copied onto the other's auxiliary side with its label
def rule.fans(same: Bool) -> Rule:
  match same:
    case True{}:
      RWire{[], [lk(ex(0n), ex(2n)), lk(ex(1n), ex(3n))]}
    case False{}:
      RWire{[Spec{KMerge{}, SFanB{}}, Spec{KMerge{}, SFanB{}}, Spec{KCopy{}, SFanA{}}, Spec{KCopy{}, SFanA{}}],
        [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n)), lk(nw(2n, 0n), ex(2n)), lk(nw(3n, 0n), ex(3n)),
         lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n)), lk(nw(3n, 1n), nw(0n, 2n)), lk(nw(3n, 2n), nw(1n, 2n))]}

# A, negative principal, meets B, positive principal; t says whether B is
# a builtin function, or for a function whether its level is A's
def rule.ap(b: NodeKind, t: Bool) -> Rule:
  match b:
    # beta: the bind's auxiliaries join crossed. t says the levels agree;
    # in a well-formed net they do, so a mismatch is stuck, an error
    case KFn{}:
      match t:
        case True{}:
          RWire{[], [lk(ex(0n), ex(3n)), lk(ex(1n), ex(2n))]}
        case False{}:
          RStuck{}
    # applying a superposition: the application is copied onto each side
    case KMerge{}:
      RWire{[Spec{KAp{}, SPayA{}}, Spec{KAp{}, SPayA{}}, Spec{KCopy{}, SFanB{}}, Spec{KMerge{}, SFanB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(3n)),
         lk(nw(2n, 0n), ex(0n)), lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n)),
         lk(nw(3n, 0n), ex(1n)), lk(nw(3n, 1n), nw(0n, 2n)), lk(nw(3n, 2n), nw(1n, 2n))]}
    # applying a builtin: a strict call, its principal on the argument,
    # waits for the argument to become data; applying other data is stuck
    case KData{}:
      match t:
        case True{}:
          RWire{[Spec{KCall{}, SPayB{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(0n, 1n), ex(1n))]}
        case False{}:
          RStuck{}
    # an application meeting a control facing it moves up past it, its
    # level adjusted, the control copied onto its argument and result
    case KLiftC{}:
      RWire{[Spec{KAp{}, SLiftA{}}, Spec{KLift{}, SPayB{}}, Spec{KLiftC{}, SPayB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(0n)), lk(nw(1n, 1n), nw(0n, 1n)),
         lk(nw(2n, 0n), ex(1n)), lk(nw(2n, 1n), nw(0n, 2n))]}
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
      RWire{[Spec{KFn{}, SPayB{}}, Spec{KFn{}, SPayB{}}, Spec{KCopy{}, SFanA{}}, Spec{KMerge{}, SFanA{}}],
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
    # a copy meeting a control facing it moves up past it, its level
    # adjusted, the control copied onto both outputs
    case KLiftC{}:
      RWire{[Spec{KCopy{}, SLiftA{}}, Spec{KLiftC{}, SPayB{}}, Spec{KLiftC{}, SPayB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(0n)), lk(nw(1n, 1n), nw(0n, 1n)),
         lk(nw(2n, 0n), ex(1n)), lk(nw(2n, 1n), nw(0n, 2n))]}
    case _:
      RStuck{}

# a strict call meets its argument
def rule.call(b: NodeKind) -> Rule:
  match b:
    case KData{}:
      RWire{[Spec{KData{}, SApply{}}], [lk(nw(0n, 0n), ex(0n))]}
    # a superposed argument: the call is copied onto each side, and the
    # results superposed under the argument's fan identity
    case KMerge{}:
      RWire{[Spec{KCall{}, SPayA{}}, Spec{KCall{}, SPayA{}}, Spec{KMerge{}, SFanB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(3n)),
         lk(nw(2n, 0n), ex(0n)), lk(nw(2n, 1n), nw(0n, 1n)), lk(nw(2n, 2n), nw(1n, 1n))]}
    case KEraP{}:
      RWire{[Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
    # a call carries no level: it moves past a control facing it, which
    # goes on to its result
    case KLiftC{}:
      RWire{[Spec{KCall{}, SPayA{}}, Spec{KLiftC{}, SPayB{}}],
        [lk(nw(0n, 0n), ex(2n)), lk(nw(1n, 0n), ex(0n)), lk(nw(1n, 1n), nw(0n, 1n))]}
    case _:
      RStuck{}

# a control node facing the source meets what flows down its wire: data
# pass unchanged; a merge or function passes with its level adjusted, the
# control copied onto each wire behind it: facing the source on a wire it
# takes in, facing the consumers on a function's argument wire, whose uses
# lie behind it too; t, for a control facing it, says they cancel
def rule.lift(b: NodeKind, t: Bool) -> Rule:
  match b:
    case KData{}:
      RWire{[Spec{KData{}, SPayB{}}], [lk(nw(0n, 0n), ex(0n))]}
    case KEraP{}:
      RWire{[Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
    case KMerge{}:
      RWire{[Spec{KMerge{}, SLiftB{}}, Spec{KLift{}, SPayA{}}, Spec{KLift{}, SPayA{}}],
        [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(2n)), lk(nw(1n, 1n), nw(0n, 1n)),
         lk(nw(2n, 0n), ex(3n)), lk(nw(2n, 1n), nw(0n, 2n))]}
    case KFn{}:
      RWire{[Spec{KFn{}, SLiftB{}}, Spec{KLift{}, SPayA{}}, Spec{KLiftC{}, SPayA{}}],
        [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(2n)), lk(nw(1n, 1n), nw(0n, 1n)),
         lk(nw(2n, 0n), ex(3n)), lk(nw(2n, 1n), nw(0n, 2n))]}
    # two controls facing each other: one kind and index cancel; else
    # each crosses the other, the higher index adjusted by the lower
    case KLiftC{}:
      match t:
        case True{}:
          RWire{[], [lk(ex(0n), ex(2n))]}
        case False{}:
          RWire{[Spec{KLift{}, SLiftA{}}, Spec{KLiftC{}, SLiftB{}}],
            [lk(nw(0n, 0n), ex(2n)), lk(nw(0n, 1n), nw(1n, 1n)), lk(nw(1n, 0n), ex(0n))]}
    case _:
      RStuck{}

# the net's root meets a control facing it: it carries no level, so it
# takes the control's place, as an eraser does; anything else is the
# result, or stuck
def rule.root(b: NodeKind) -> Rule:
  match b:
    case KLiftC{}:
      RWire{[Spec{KRoot{}, SNone{}}], [lk(nw(0n, 0n), ex(2n))]}
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
    # erasing past a control: the eraser takes its place
    case KLiftC{}:
      RWire{[Spec{KEraN{}, SNone{}}], [lk(nw(0n, 0n), ex(2n))]}
    case _:
      RStuck{}

# the rule for A meeting B, both full kinds, A's principal negative. t
# tests the payloads: for two fans, whether they are residuals of one
# duplication; for an application meeting data, whether the data is a
# builtin function; for an application meeting a function, whether their
# levels agree. Linear fans' rules are derived from these (rule, below).
def rule.full(a: NodeKind, b: NodeKind, t: Bool) -> Rule:
  match a:
    case KAp{}:
      rule.ap(b, t)
    case KCopy{}:
      rule.copy(b, t)
    case KEraN{}:
      rule.era(b)
    case KCall{}:
      rule.call(b)
    case KLift{}:
      rule.lift(b, t)
    case KRoot{}:
      rule.root(b)
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

# Linear fans
# ===========
#
# heap-strategies.erasure.rules in docs/plans/HeapModel_2026-10-27.md. A
# fan one of whose auxiliary ports an eraser met keeps the other: a linear
# fan of two ports, named for the side it keeps (KCopyL keeps a copy's
# left output, its port 1, the right erased; KMergeR a merge's right
# input, port 2 once, the left an error value). Its rules are derived
# from the full fan's: the full rule rewrites; an eraser stands where the
# dead side was, a consuming one for a copy's output, a providing one for
# a merge's input; erasures and events run among the new nodes until none
# can; and a fan left with one side erased becomes linear. The events, an
# eraser's principal facing an auxiliary port: an application, call or
# control whose output it takes becomes an eraser of what that took in; a
# fan both of whose sides are erased becomes an eraser. A linear fan stays
# while its full fan would: it selects its side at each fan of its
# identity it meets, which no local test can tell are all met, so it goes
# only where the full fan would go, annihilating or at a leaf.

# a rule's new nodes and links as they are rewritten; a node gone is free
type G is Data:
  G{xs: List<&2, Spec>, ls: List<&2, Link>}

def spec_src(xs: List<&2, Spec>, j: Nat) -> Src:
  match xs j:
    case Nil{} _:
      SNone{}
    case Con{Spec{k, s}, t} 0n:
      s
    case Con{h, t} 1n+i:
      spec_src(t, i)

def set_kind(xs: List<&2, Spec>, j: Nat, +k: NodeKind) -> List<&2, Spec>:
  match xs j:
    case Nil{} _:
      Nil{}
    case Con{Spec{k0, s}, t} 0n:
      Con{Spec{k, s}, t}
    case Con{h, t} 1n+i:
      Con{h, set_kind(t, i, k)}

def lf.one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def lf.one(onx: Bool, ony: Bool, x: End, y: End) -> Maybe<&2, End>:
  match onx ony:
    case True{} _:
      Some{y}
    case False{} True{}:
      Some{x}
    case False{} False{}:
      None{}

def lf.first(a: Maybe<&2, End>, b: Maybe<&2, End>) -> Maybe<&2, End>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# the end linked to e
def lf.peer(ls: List<&2, Link>, +e: End) -> Maybe<&2, End>:
  match ls:
    case Nil{}:
      None{}
    case Con{Link{+x, +y}, t}:
      lf.first(lf.one(end_eq(x, e), end_eq(y, e), x, y), lf.peer(t, e))

def lf.or_end(m: Maybe<&2, End>) -> End:
  match m:
    case Some{x}:
      x
    case None{}:
      Ext{9n}

# is e a port of node j?
def lf.at(+j: Nat, e: End) -> Bool:
  match e:
    case Ext{i}:
      False{}
    case New{i, p}:
      nat_eq(i, j)

def lf.keep(+gone: Bool, l: Link, rest: List<&2, Link>) -> List<&2, Link>:
  match gone:
    case True{}:
      rest
    case False{}:
      Con{l, rest}

# the links but those at node j
def lf.unlink(ls: List<&2, Link>, +j: Nat) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{+x, +y}, t}:
      lf.keep(lf.at(j, x) || lf.at(j, y), Link{x, y}, lf.unlink(t, j))

# the links but the one at end e
def lf.cut(ls: List<&2, Link>, +e: End) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{+x, +y}, t}:
      lf.keep(end_eq(x, e) || end_eq(y, e), Link{x, y}, lf.cut(t, e))

def lf.rep.n(+hit: Bool, +x: Nat, +y: Nat) -> Nat:
  match hit:
    case True{}:
      y
    case False{}:
      x

def lf.rep(+hit: Bool, e: End, +to: End) -> End:
  match hit:
    case True{}:
      to
    case False{}:
      e

# every end old renamed to
def lf.rename(ls: List<&2, Link>, +old: End, +to: End) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{+x, +y}, t}:
      Con{Link{lf.rep(end_eq(x, old), x, to), lf.rep(end_eq(y, old), y, to)}, lf.rename(t, old, to)}

def lf.kind(g: G, +j: Nat) -> NodeKind:
  match g:
    case G{xs, ls}:
      spec_kind(xs, j)

def lf.size(g: G) -> Nat:
  match g:
    case G{xs, ls}:
      List.length(&2, Spec, xs)

# Rewriting within a rule's new nodes

# an end of rule applied to nodes a (A) and b (B), its new nodes numbered
# from n0: an external peer is the peer of a's or b's auxiliary port
def lf.tr(+ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat, e: End) -> End:
  match e:
    case Ext{i}:
      match i:
        case 0n:
          lf.or_end(lf.peer(ls, New{a, 1n}))
        case 1n:
          lf.or_end(lf.peer(ls, New{a, 2n}))
        case 2n:
          lf.or_end(lf.peer(ls, New{b, 1n}))
        case _:
          lf.or_end(lf.peer(ls, New{b, 2n}))
    case New{j, p}:
      New{Nat.add(n0, j), p}

def lf.trs(ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat) -> List<&2, Link>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Link{x, y}, t}:
      Con{Link{lf.tr(ls, a, b, n0, x), lf.tr(ls, a, b, n0, y)}, lf.trs(t, ls, a, b, n0)}

# nodes a and b of g rewritten by r, if it rewrites
def lf.apply(r: Rule, g: G, +a: Nat, +b: Nat) -> Maybe<&2, G>:
  match r g:
    case RWire{ys, ms} G{+xs, +ls}:
      Some{G{List.append(&2, Spec, set_kind(set_kind(xs, a, KFree{}), b, KFree{}), ys),
        List.append(&2, Link, lf.unlink(lf.unlink(ls, a), b), lf.trs(ms, ls, a, b, List.length(&2, Spec, xs)))}}
    case RStuck{} G{xs, ls}:
      None{}

# eraser e gone, node j become an eraser of kind k
def lf.become(g: G, +e: Nat, +j: Nat, +k: NodeKind) -> G:
  match g:
    case G{xs, ls}:
      G{set_kind(set_kind(xs, j, k), e, KFree{}), lf.unlink(ls, e)}

# an application whose result eraser e takes: an eraser facing its
# function, and a new one for its argument
def lf.ap_dead(g: G, +e: Nat, +j: Nat) -> G:
  match g:
    case G{+xs, +ls}:
      G{List.append(&2, Spec, set_kind(set_kind(xs, j, KEraN{}), e, KFree{}), [Spec{KEraN{}, SNone{}}]),
        Con{Link{lf.or_end(lf.peer(ls, New{j, 1n})), New{List.length(&2, Spec, xs), 0n}}, lf.cut(lf.unlink(ls, e), New{j, 1n})}}

# the eraser at end x, of kind k, if there is one
def lf.er.k(k: NodeKind, +want: NodeKind, +f: Nat) -> Maybe<&2, Nat>:
  match k want:
    case KEraN{} KEraN{}:
      Some{f}
    case KEraP{} KEraP{}:
      Some{f}
    case _ _:
      None{}

def lf.er(+g: G, x: Maybe<&2, End>, +want: NodeKind) -> Maybe<&2, Nat>:
  match x:
    case Some{e}:
      match e:
        case New{+f, p}:
          match p:
            case 0n:
              lf.er.k(lf.kind(g, f), want, f)
            case _:
              None{}
        case Ext{i}:
          None{}
    case None{}:
      None{}

# a fan whose other side eraser f takes as well: an eraser itself
def lf.both(f: Maybe<&2, Nat>, g: G, +e: Nat, +j: Nat, +k: NodeKind) -> Maybe<&2, G>:
  match f:
    case Some{+f2}:
      Some{lf.become(lf.become(g, e, j, k), f2, j, k)}
    case None{}:
      None{}

def lf.other(p: Nat) -> Nat:
  match p:
    case 1n:
      2n
    case _:
      1n

def lf.ev.ap(ok: Bool, g: G, +e: Nat, +j: Nat) -> Maybe<&2, G>:
  match ok:
    case True{}:
      Some{lf.ap_dead(g, e, j)}
    case False{}:
      None{}

# an event: eraser e of kind ke facing port p of node j, of kind kj
def lf.ev(ke: NodeKind, kj: NodeKind, +g: G, +e: Nat, +j: Nat, +p: Nat) -> Maybe<&2, G>:
  match ke kj:
    case KEraN{} KAp{}:
      lf.ev.ap(nat_eq(p, 2n), g, e, j)
    case KEraN{} KCall{}:
      Some{lf.become(g, e, j, KEraN{})}
    case KEraN{} KLift{}:
      Some{lf.become(g, e, j, KEraN{})}
    case KEraN{} KCopy{}:
      match g:
        case G{+xs, +ls}:
          lf.both(lf.er(G{xs, ls}, lf.peer(ls, New{j, lf.other(p)}), KEraN{}), G{xs, ls}, e, j, KEraN{})
    case KEraP{} KMerge{}:
      match g:
        case G{+xs, +ls}:
          lf.both(lf.er(G{xs, ls}, lf.peer(ls, New{j, lf.other(p)}), KEraP{}), G{xs, ls}, e, j, KEraP{})
    case _ _:
      None{}

# eraser e of kind ke facing end x: an erasure where x is a principal
# port, an event where it is an auxiliary one
def lf.at_j(p: Nat, ke: NodeKind, kj: NodeKind, +g: G, +e: Nat, +j: Nat) -> Maybe<&2, G>:
  match p:
    case 0n:
      match ke:
        case KEraN{}:
          lf.apply(rule.full(KEraN{}, kj, True{}), g, e, j)
        case _:
          lf.apply(rule.full(kj, KEraP{}, True{}), g, j, e)
    case 1n+q:
      lf.ev(ke, kj, g, e, j, 1n+q)

def lf.at_e(ke: NodeKind, +g: G, +e: Nat, x: Maybe<&2, End>) -> Maybe<&2, G>:
  match x:
    case Some{y}:
      match y:
        case New{+j, p}:
          lf.at_j(p, ke, lf.kind(g, j), g, e, j)
        case Ext{i}:
          None{}
    case None{}:
      None{}

def lf.try.k(k: NodeKind, +g: G, +j: Nat, x: Maybe<&2, End>) -> Maybe<&2, G>:
  match k:
    case KEraN{}:
      lf.at_e(KEraN{}, g, j, x)
    case KEraP{}:
      lf.at_e(KEraP{}, g, j, x)
    case _:
      None{}

# what node j, if an eraser, can run
def lf.try(+g: G, +j: Nat) -> Maybe<&2, G>:
  match g:
    case G{+xs, +ls}:
      lf.try.k(spec_kind(xs, j), G{xs, ls}, j, lf.peer(ls, New{j, 0n}))

# the first erasure or event any node from j on can run, n nodes left
def lf.scan(n: Nat, r: Maybe<&2, G>, +g: G, +j: Nat) -> Maybe<&2, G>:
  match n r:
    case _ Some{g2}:
      Some{g2}
    case 0n None{}:
      None{}
    case 1n+m None{}:
      lf.scan(m, lf.try(g, 1n+j), g, 1n+j)

# erasures and events run until none can; none if n steps are not enough
def lf.norm(n: Nat, r: Maybe<&2, G>, +g: G) -> Maybe<&2, G>:
  match n r:
    case _ None{}:
      Some{g}
    case 0n Some{g2}:
      None{}
    case 1n+m Some{+g2}:
      lf.norm(m, lf.scan(lf.size(g2), lf.try(g2, 0n), g2, 0n), g2)

# Fans made linear

def lf.shift(+right: Bool, ls: List<&2, Link>, +j: Nat) -> List<&2, Link>:
  match right:
    case True{}:
      lf.rename(ls, New{j, 2n}, New{j, 1n})
    case False{}:
      ls

# fan j keeping one side, eraser f on the other absorbed: of kind k,
# its kept port 1 (right says it was port 2)
def lf.keepside(+k: NodeKind, g: G, +j: Nat, +f: Nat, +right: Bool) -> G:
  match g:
    case G{xs, ls}:
      G{set_kind(set_kind(xs, j, k), f, KFree{}), lf.shift(right, lf.unlink(ls, f), j)}

def lf.mark2(kj: NodeKind, +g: G, +j: Nat, f1: Maybe<&2, Nat>, f2: Maybe<&2, Nat>) -> G:
  match kj f1 f2:
    case KCopy{} Some{f} None{}:
      lf.keepside(KCopyR{}, g, j, f, True{})
    case KCopy{} None{} Some{f}:
      lf.keepside(KCopyL{}, g, j, f, False{})
    case KMerge{} Some{f} None{}:
      lf.keepside(KMergeR{}, g, j, f, True{})
    case KMerge{} None{} Some{f}:
      lf.keepside(KMergeL{}, g, j, f, False{})
    case _ _ _:
      g

def lf.dead_er(k: NodeKind) -> NodeKind:
  match k:
    case KMerge{}:
      KEraP{}
    case _:
      KEraN{}

def lf.mark1(+g: G, +j: Nat) -> G:
  match g:
    case G{+xs, +ls}:
      lf.mark2(spec_kind(xs, j), G{xs, ls}, j,
        lf.er(G{xs, ls}, lf.peer(ls, New{j, 1n}), lf.dead_er(spec_kind(xs, j))),
        lf.er(G{xs, ls}, lf.peer(ls, New{j, 2n}), lf.dead_er(spec_kind(xs, j))))

# every fan from node j on, n nodes, with one side erased made linear
def lf.mark(n: Nat, g: G, +j: Nat) -> G:
  match n:
    case 0n:
      g
    case 1n+m:
      lf.mark(m, lf.mark1(g, j), 1n+j)

# The rule as derived

def is_free_k(k: NodeKind) -> Bool:
  match k:
    case KFree{}:
      True{}
    case _:
      False{}

# nodes before index j that remain
def lf.before(xs: List<&2, Spec>, j: Nat) -> Nat:
  match xs j:
    case Nil{} _:
      0n
    case Con{Spec{k, s}, t} 0n:
      0n
    case Con{Spec{k, s}, t} 1n+i:
      Nat.add(lf.one_if(Bool.not(is_free_k(k))), lf.before(t, i))

# an end renumbered, the nodes gone left out; external peers past a
# linear fan's one side renumbered as its own (sa: A keeps its right
# output, Ext 1 is its Ext 0; sb: B keeps its right input, Ext 3 its 2)
def lf.cend(+xs: List<&2, Spec>, +sa: Bool, +sb: Bool, e: End) -> End:
  match e:
    case New{j, p}:
      New{lf.before(xs, j), p}
    case Ext{+i}:
      lf.rep(sa && nat_eq(i, 1n), lf.rep(sb && nat_eq(i, 3n), Ext{i}, Ext{2n}), Ext{0n})

def lf.clinks(ls: List<&2, Link>, +xs: List<&2, Spec>, +sa: Bool, +sb: Bool) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{x, y}, t}:
      Con{Link{lf.cend(xs, sa, sb, x), lf.cend(xs, sa, sb, y)}, lf.clinks(t, xs, sa, sb)}

def lf.cnodes.k(+gone: Bool, x: Spec, rest: List<&2, Spec>) -> List<&2, Spec>:
  match gone:
    case True{}:
      rest
    case False{}:
      Con{x, rest}

def lf.cnodes(xs: List<&2, Spec>) -> List<&2, Spec>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Spec{+k, s}, t}:
      lf.cnodes.k(is_free_k(k), Spec{k, s}, lf.cnodes(t))

def lf.out(g: G, +sa: Bool, +sb: Bool) -> Rule:
  match g:
    case G{+xs, ls}:
      RWire{lf.cnodes(xs), lf.clinks(ls, xs, sa, sb)}

def lf.fin(m: Maybe<&2, G>, +sa: Bool, +sb: Bool) -> Rule:
  match m:
    case None{}:
      RStuck{}
    case Some{+g}:
      lf.out(lf.mark(lf.size(g), g, 0n), sa, sb)

# a linear fan's full kind
def lf.full(+k: NodeKind) -> NodeKind:
  match k:
    case KCopyL{}:
      KCopy{}
    case KCopyR{}:
      KCopy{}
    case KMergeL{}:
      KMerge{}
    case KMergeR{}:
      KMerge{}
    case _:
      k

# where the dead side was, as the full rule numbers its external peers:
# A's, a copy's erased output; B's, a merge's erased input
def lf.dead_a(k: NodeKind) -> Maybe<&2, Nat>:
  match k:
    case KCopyL{}:
      Some{1n}
    case KCopyR{}:
      Some{0n}
    case _:
      None{}

def lf.dead_b(k: NodeKind) -> Maybe<&2, Nat>:
  match k:
    case KMergeL{}:
      Some{3n}
    case KMergeR{}:
      Some{2n}
    case _:
      None{}

def lf.right_a(k: NodeKind) -> Bool:
  match k:
    case KCopyR{}:
      True{}
    case _:
      False{}

def lf.right_b(k: NodeKind) -> Bool:
  match k:
    case KMergeR{}:
      True{}
    case _:
      False{}

# an eraser of kind k standing where external peer d was
def lf.attach(m: Maybe<&2, Nat>, g: G, +k: NodeKind) -> G:
  match m g:
    case Some{d} G{+xs, ls}:
      G{List.append(&2, Spec, xs, [Spec{k, SNone{}}]), lf.rename(ls, Ext{d}, New{List.length(&2, Spec, xs), 0n})}
    case None{} G{xs, ls}:
      G{xs, ls}

def lf.derive.g(+g: G, +a: NodeKind, +b: NodeKind) -> Rule:
  lf.fin(lf.norm(16n, lf.scan(lf.size(g), lf.try(g, 0n), g, 0n), g), lf.right_a(a), lf.right_b(b))

def lf.derive.r(r: Rule, +a: NodeKind, +b: NodeKind) -> Rule:
  match r:
    case RStuck{}:
      RStuck{}
    case RWire{xs, ls}:
      lf.derive.g(lf.attach(lf.dead_b(b), lf.attach(lf.dead_a(a), G{xs, ls}, KEraN{}), KEraP{}), a, b)

# a rule with a linear fan, derived from its full fan's
def lf.derive(+a: NodeKind, +b: NodeKind, t: Bool) -> Rule:
  lf.derive.r(rule.full(lf.full(a), lf.full(b), t), a, b)

def is_lin(k: NodeKind) -> Bool:
  match k:
    case KCopyL{}:
      True{}
    case KCopyR{}:
      True{}
    case KMergeL{}:
      True{}
    case KMergeR{}:
      True{}
    case _:
      False{}

# A, of a full kind with a negative principal, meeting B: a linear
# merge's rule derived
def rule.b(+a: NodeKind, b: NodeKind, t: Bool) -> Rule:
  match b:
    case KMergeL{}:
      lf.derive(a, KMergeL{}, t)
    case KMergeR{}:
      lf.derive(a, KMergeR{}, t)
    case _:
      rule.full(a, b, t)

# the rule for A meeting B, A's principal negative, t testing the payloads
# as rule.full says: a full fan's rule, or a linear one's derived from it;
# a kind whose principal is positive is never A, and stuck as one
def rule(a: NodeKind, b: NodeKind, t: Bool) -> Rule:
  match a:
    case KCopyL{}:
      lf.derive(KCopyL{}, b, t)
    case KCopyR{}:
      lf.derive(KCopyR{}, b, t)
    case KAp{}:
      rule.b(KAp{}, b, t)
    case KCopy{}:
      rule.b(KCopy{}, b, t)
    case KEraN{}:
      rule.b(KEraN{}, b, t)
    case KCall{}:
      rule.b(KCall{}, b, t)
    case KLift{}:
      rule.b(KLift{}, b, t)
    case KRoot{}:
      rule.b(KRoot{}, b, t)
    case _:
      RStuck{}

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

def is_stuck(r: Rule) -> Bool:
  match r:
    case RStuck{}:
      True{}
    case _:
      False{}

def made_at_most_one(r: Rule) -> Bool:
  match r:
    case RWire{xs, ls}:
      Nat.is_lt(List.length(&2, Spec, xs), 2n)
    case RStuck{}:
      True{}

# could this end be a principal port once linked? an external peer may be
# any node's port; a new node's, only its port 0
def may_pri(e: End) -> Bool:
  match e:
    case Ext{i}:
      True{}
    case New{j, +p}:
      nat_eq(p, 0n)

def pri_links(ls: List<&2, Link>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{Link{x, y}, t}:
      Nat.add(one_if(may_pri(x) && may_pri(y)), pri_links(t))

# the most active pairs a rule's rewrite makes: its links that may join
# two principal ports, each of which an eager strategy notes
# (gen_krules.bend); a commutation makes four, each new node facing an
# external peer
def pairs_made(r: Rule) -> Nat:
  match r:
    case RWire{xs, ls}:
      pri_links(ls)
    case RStuck{}:
      0n

# where the payload test decides whether A >< B is stuck, the rule that
# rewrites makes at most one node: the kernel's walk tells a rewrite from
# a stuck pair by B's slot alone (kstrat.bend, Demand)
def tested_small(+a: NodeKind, +b: NodeKind) -> Bool:
  Bool.not(Bool.not(is_stuck(rule(a, b, True{}))) && is_stuck(rule(a, b, False{})) ||
      is_stuck(rule(a, b, True{})) && Bool.not(is_stuck(rule(a, b, False{})))) ||
    made_at_most_one(rule(a, b, True{})) && made_at_most_one(rule(a, b, False{}))

def lf.same(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def made(r: Rule) -> Nat:
  match r:
    case RWire{xs, ls}:
      List.length(&2, Spec, xs)
    case RStuck{}:
      0n

# a linear fan rewrites exactly where its full fan does (law
# rules_linear_rewrites)
def lin_rewrites(+a: NodeKind, +b: NodeKind, +t: Bool) -> Bool:
  lf.same(is_stuck(rule(a, b, t)), is_stuck(rule.full(lf.full(a), lf.full(b), t))) || Bool.not(is_lin(a) || is_lin(b))

# where the full fan's rule makes nodes, the linear fan's makes fewer:
# nothing is copied for the side erased (law rules_linear_fewer)
def lin_fewer(+a: NodeKind, +b: NodeKind, +t: Bool) -> Bool:
  nat_eq(made(rule.full(lf.full(a), lf.full(b), t)), 0n) ||
    (Bool.not(is_lin(a) || is_lin(b)) || Nat.is_lt(made(rule(a, b, t)), made(rule.full(lf.full(a), lf.full(b), t))))

# every end the rule must link is linked exactly once, and nothing else
def linear(+a: NodeKind, +b: NodeKind, r: Rule) -> Bool:
  match r:
    case RWire{+xs, +ls}:
      all_once(ls, expected(a, b, xs)) && nat_eq(ends_count(ls), List.length(&2, End, expected(a, b, xs)))
    case _:
      True{}

# the ends of a rule's links, in order, two a link
def ends(ls: List<&2, Link>) -> List<&2, End>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{x, y}, t}:
      x <> (y <> ends(t))

def end_mem(+e: End, es: List<&2, End>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{x, t}:
      end_eq(x, e) || end_mem(e, t)

def ends_distinct(es: List<&2, End>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.not(end_mem(x, t)) && ends_distinct(t)

# every end of xs is in es
def all_in(xs: List<&2, End>, +es: List<&2, End>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      end_mem(x, es) && all_in(t, es)

# the ends the rule links are the ends it must link, none twice: what
# linear says, in the form the net's wiring law (wiring.bend) takes
def exact(+a: NodeKind, +b: NodeKind, r: Rule) -> Bool:
  match r:
    case RWire{+xs, +ls}:
      ends_distinct(ends(ls)) && (all_in(ends(ls), expected(a, b, xs)) && all_in(expected(a, b, xs), ends(ls)))
    case _:
      True{}

# Peers inside the pair (knet.bend's link_pairs)
# ===============================================
#
# A peer of the pair's auxiliary ports may be a port of the pair itself,
# a's port linked to b's or to a's other: its Ext end then stands for the
# Ext end of the port it faces (net.bend's partner). The kernel links the
# rule's links whose ends both face outside, then, for each such pair of
# Ext ends, i below j, joins the ends the rule links to Ext i and to Ext
# j. Where either is itself inside, the rule's links and the pair's own
# close a loop of wire, which vanishes; where either is missing, an error. A pattern says
# which Ext ends face inside, and their partners: none, one link among
# the pair's auxiliary ports, or two.
type Pat is Data:
  PNone{}
  P01{}
  P02{}
  P03{}
  P12{}
  P13{}
  P23{}
  P01_23{}
  P02_13{}
  P03_12{}

# the partner of Ext i under pattern p, None facing outside
def pat_at(p: Pat, i: Nat) -> Maybe<&2, Nat>:
  match p:
    case PNone{}:
      None{}
    case P01{}:
      match i:
        case 0n:
          Some{1n}
        case 1n:
          Some{0n}
        case _:
          None{}
    case P02{}:
      match i:
        case 0n:
          Some{2n}
        case 2n:
          Some{0n}
        case _:
          None{}
    case P03{}:
      match i:
        case 0n:
          Some{3n}
        case 3n:
          Some{0n}
        case _:
          None{}
    case P12{}:
      match i:
        case 1n:
          Some{2n}
        case 2n:
          Some{1n}
        case _:
          None{}
    case P13{}:
      match i:
        case 1n:
          Some{3n}
        case 3n:
          Some{1n}
        case _:
          None{}
    case P23{}:
      match i:
        case 2n:
          Some{3n}
        case 3n:
          Some{2n}
        case _:
          None{}
    case P01_23{}:
      match i:
        case 0n:
          Some{1n}
        case 1n:
          Some{0n}
        case 2n:
          Some{3n}
        case 3n:
          Some{2n}
        case _:
          None{}
    case P02_13{}:
      match i:
        case 0n:
          Some{2n}
        case 1n:
          Some{3n}
        case 2n:
          Some{0n}
        case 3n:
          Some{1n}
        case _:
          None{}
    case P03_12{}:
      match i:
        case 0n:
          Some{3n}
        case 1n:
          Some{2n}
        case 2n:
          Some{1n}
        case 3n:
          Some{0n}
        case _:
          None{}

# an end facing a port of the pair
def pat_in(+p: Pat, e: End) -> Bool:
  match e:
    case Ext{i}:
      Maybe.is_some(&2, Nat, pat_at(p, i))
    case New{j, q}:
      False{}

def plain.k(+keep: Bool, l: Link, rest: List<&2, Link>) -> List<&2, Link>:
  match keep:
    case True{}:
      l <> rest
    case False{}:
      rest

# the rule's links with both ends facing outside (knet.bend's link_plain)
def plain(+p: Pat, ls: List<&2, Link>) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{+u, +v}, t}:
      plain.k(Bool.not(pat_in(p, u) || pat_in(p, v)), Link{u, v}, plain(p, t))

def other1(onx: Bool, ony: Bool, x: End, y: End) -> Maybe<&2, End>:
  match onx ony:
    case True{} _:
      Some{y}
    case False{} True{}:
      Some{x}
    case False{} False{}:
      None{}

def first_of(a: Maybe<&2, End>, b: Maybe<&2, End>) -> Maybe<&2, End>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# the end the rule links to Ext i (net.bend's other)
def other_of(ls: List<&2, Link>, +i: Nat) -> Maybe<&2, End>:
  match ls:
    case Nil{}:
      None{}
    case Con{Link{+x, +y}, t}:
      first_of(other1(end_eq(x, Ext{i}), end_eq(y, Ext{i}), x, y), other_of(t, i))

def pair_link(+bad: Bool, u: End, v: End, rest: Maybe<&2, List<&2, Link>>) -> Maybe<&2, List<&2, Link>>:
  match bad rest:
    case True{} _:
      rest
    case False{} Some{t}:
      Some{Link{u, v} <> t}
    case False{} None{}:
      None{}

def pair_ends(oi: Maybe<&2, End>, oj: Maybe<&2, End>, +p: Pat, rest: Maybe<&2, List<&2, Link>>) -> Maybe<&2, List<&2, Link>>:
  match oi oj:
    case Some{+u} Some{+v}:
      pair_link(pat_in(p, u) || pat_in(p, v), u, v, rest)
    case _ _:
      None{}

def pair_go(lt: Bool, +i: Nat, +j: Nat, +p: Pat, +ls: List<&2, Link>, rest: Maybe<&2, List<&2, Link>>) -> Maybe<&2, List<&2, Link>>:
  match lt:
    case True{}:
      pair_ends(other_of(ls, i), other_of(ls, j), p, rest)
    case False{}:
      rest

def pair_at(pt: Maybe<&2, Nat>, +i: Nat, +p: Pat, +ls: List<&2, Link>, rest: Maybe<&2, List<&2, Link>>) -> Maybe<&2, List<&2, Link>>:
  match pt:
    case None{}:
      rest
    case Some{+j}:
      pair_go(Nat.is_lt(i, j), i, j, p, ls, rest)

# the joined pairs from Ext i, n of them (knet.bend's link_pairs)
def pairs(n: Nat, +i: Nat, +p: Pat, +ls: List<&2, Link>) -> Maybe<&2, List<&2, Link>>:
  match n:
    case 0n:
      Some{Nil{}}
    case 1n+k:
      pair_at(pat_at(p, i), i, p, ls, pairs(k, 1n+i, p, ls))

def contract.go(pl: List<&2, Link>, m: Maybe<&2, List<&2, Link>>) -> Maybe<&2, List<&2, Link>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{List.append(&2, Link, pl, t)}

# the links the kernel makes of the rule's under pattern p, None where it
# reports an error: the plain links, then the joined pairs
def contract(+p: Pat, +ls: List<&2, Link>) -> Maybe<&2, List<&2, Link>>:
  contract.go(plain(p, ls), pairs(4n, 0n, p, ls))

# the Ext ends a rule may link: a's auxiliary peers, then b's
def ext_ends(+a: NodeKind, +b: NodeKind) -> List<&2, End>:
  List.append(&2, End, aux_ends(Nat.sub(arity(a), 1n), 0n), aux_ends(Nat.sub(arity(b), 1n), 2n))

def outer.k(+keep: Bool, e: End, rest: List<&2, End>) -> List<&2, End>:
  match keep:
    case True{}:
      e <> rest
    case False{}:
      rest


# the ends of es facing outside
def outer(+p: Pat, es: List<&2, End>) -> List<&2, End>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      outer.k(Bool.not(pat_in(p, e)), e, outer(p, t))

def exact_in.m(m: Maybe<&2, List<&2, Link>>, +a: NodeKind, +b: NodeKind, +p: Pat, +xs: List<&2, Spec>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+ls}:
      ends_distinct(ends(ls)) && (all_in(ends(ls), List.append(&2, End, outer(p, ext_ends(a, b)), new_ends(xs, 0n))) &&
        all_in(List.append(&2, End, outer(p, ext_ends(a, b)), new_ends(xs, 0n)), ends(ls)))

# under pattern p, the links the kernel makes link exactly the ends left
# to link, none twice: the outside peers and the new ports; or the kernel
# reports an error
def exact_in(+a: NodeKind, +b: NodeKind, +p: Pat, r: Rule) -> Bool:
  match r:
    case RWire{+xs, +ls}:
      exact_in.m(contract(p, ls), a, b, p, xs)
    case _:
      True{}

# a pattern the pair can have: every Ext end it puts inside is one the
# pair's arities give it
def pat_ok.i(+a: NodeKind, +b: NodeKind, +p: Pat, +i: Nat) -> Bool:
  Bool.not(Maybe.is_some(&2, Nat, pat_at(p, i))) || end_mem(Ext{i}, ext_ends(a, b))

def pat_ok(+a: NodeKind, +b: NodeKind, +p: Pat) -> Bool:
  pat_ok.i(a, b, p, 0n) && (pat_ok.i(a, b, p, 1n) && (pat_ok.i(a, b, p, 2n) && pat_ok.i(a, b, p, 3n)))

# exact_in under every pattern the pair can have
def exact_pairs(+a: NodeKind, +b: NodeKind, +r: Rule) -> Bool:
  ((exact_in(a, b, PNone{}, r) || Bool.not(pat_ok(a, b, PNone{}))) && ((exact_in(a, b, P01{}, r) || Bool.not(pat_ok(a, b, P01{}))) && ((exact_in(a, b, P02{}, r) || Bool.not(pat_ok(a, b, P02{}))) && ((exact_in(a, b, P03{}, r) || Bool.not(pat_ok(a, b, P03{}))) && ((exact_in(a, b, P12{}, r) || Bool.not(pat_ok(a, b, P12{}))) && ((exact_in(a, b, P13{}, r) || Bool.not(pat_ok(a, b, P13{}))) && ((exact_in(a, b, P23{}, r) || Bool.not(pat_ok(a, b, P23{}))) && ((exact_in(a, b, P01_23{}, r) || Bool.not(pat_ok(a, b, P01_23{}))) && ((exact_in(a, b, P02_13{}, r) || Bool.not(pat_ok(a, b, P02_13{}))) && (exact_in(a, b, P03_12{}, r) || Bool.not(pat_ok(a, b, P03_12{}))))))))))))

# the kernel joins a rule's links under pattern p without an error
def contracts(+p: Pat, r: Rule) -> Bool:
  match r:
    case RWire{xs, +ls}:
      Maybe.is_some(&2, List<&2, Link>, contract(p, ls))
    case _:
      True{}

# contracts under every pattern the pair can have
def total_pairs(+a: NodeKind, +b: NodeKind, +r: Rule) -> Bool:
  ((contracts(PNone{}, r) || Bool.not(pat_ok(a, b, PNone{}))) && ((contracts(P01{}, r) || Bool.not(pat_ok(a, b, P01{}))) && ((contracts(P02{}, r) || Bool.not(pat_ok(a, b, P02{}))) && ((contracts(P03{}, r) || Bool.not(pat_ok(a, b, P03{}))) && ((contracts(P12{}, r) || Bool.not(pat_ok(a, b, P12{}))) && ((contracts(P13{}, r) || Bool.not(pat_ok(a, b, P13{}))) && ((contracts(P23{}, r) || Bool.not(pat_ok(a, b, P23{}))) && ((contracts(P01_23{}, r) || Bool.not(pat_ok(a, b, P01_23{}))) && ((contracts(P02_13{}, r) || Bool.not(pat_ok(a, b, P02_13{}))) && (contracts(P03_12{}, r) || Bool.not(pat_ok(a, b, P03_12{}))))))))))))

# Events
# ======
#
# heap-strategies.erasure.events in docs/plans/HeapModel_2026-10-27.md.
# An eraser whose principal faces an auxiliary port forms no active pair,
# so no rule fires: the kernel looks at the links rules make, as control
# fusion does, and runs an event. As a rule, A is the node and B the
# eraser facing A's port p, A's other ports, in order, external peers 0
# and 1; the kernel puts the first new node in A's slot, so the node
# changes its kind in place. An application whose result is erased
# becomes an eraser facing its function, the eraser moving to its
# argument; a call or control whose output is erased, an eraser facing
# what it took in; a copy one of whose outputs is erased, a linear copy
# keeping the other, and a linear copy whose output is erased, an eraser;
# a merge one of whose inputs is an error value, a linear merge keeping
# the other, and a linear merge whose input is one, an error value.

def ev.ap(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraN{}:
      match p:
        case 2n:
          RWire{[Spec{KEraN{}, SNone{}}, Spec{KEraN{}, SNone{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(1n, 0n), ex(1n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

# a call's or a control's output erased
def ev.out(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraN{}:
      match p:
        case 1n:
          RWire{[Spec{KEraN{}, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

def ev.copy(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraN{}:
      match p:
        case 1n:
          RWire{[Spec{KCopyR{}, SFanA{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(0n, 1n), ex(1n))]}
        case 2n:
          RWire{[Spec{KCopyL{}, SFanA{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(0n, 1n), ex(1n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

def ev.merge(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraP{}:
      match p:
        case 1n:
          RWire{[Spec{KMergeR{}, SFanA{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(0n, 1n), ex(1n))]}
        case 2n:
          RWire{[Spec{KMergeL{}, SFanA{}}], [lk(nw(0n, 0n), ex(0n)), lk(nw(0n, 1n), ex(1n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

# a linear fan's one side erased too: an eraser of what the copy took in,
# or an error value where the merge's output goes
def ev.lin(+e: NodeKind, b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraN{}:
      match p:
        case 1n:
          RWire{[Spec{e, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
        case _:
          RStuck{}
    case KEraP{}:
      match p:
        case 1n:
          RWire{[Spec{e, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

def ev.fans(+copy: Bool, b: NodeKind, p: Nat) -> Rule:
  match copy:
    case True{}:
      match b:
        case KEraN{}:
          ev.lin(KEraN{}, KEraN{}, p)
        case _:
          RStuck{}
    case False{}:
      match b:
        case KEraP{}:
          ev.lin(KEraP{}, KEraP{}, p)
        case _:
          RStuck{}

# the event at port p of a node of kind a, an eraser of kind b facing it
def event(a: NodeKind, b: NodeKind, p: Nat) -> Rule:
  match a:
    case KAp{}:
      ev.ap(b, p)
    case KCall{}:
      ev.out(b, p)
    case KLift{}:
      ev.out(b, p)
    case KCopy{}:
      ev.copy(b, p)
    case KCopyL{}:
      ev.fans(True{}, b, p)
    case KCopyR{}:
      ev.fans(True{}, b, p)
    case KMerge{}:
      ev.merge(b, p)
    case KMergeL{}:
      ev.fans(False{}, b, p)
    case KMergeR{}:
      ev.fans(False{}, b, p)
    case _:
      RStuck{}

# A's port numbered i among its ports other than p
def ev.port(+p: Nat, i: Nat) -> Nat:
  match i:
    case 0n:
      lf.rep.n(nat_eq(p, 0n), 0n, 1n)
    case _:
      lf.rep.n(nat_eq(p, 1n) || nat_eq(p, 0n), 1n, 2n)

def ev.end_pol(+a: NodeKind, +p: Nat, +xs: List<&2, Spec>, e: End) -> Pol:
  match e:
    case Ext{i}:
      flip(port_pol(a, ev.port(p, i)))
    case New{j, q}:
      port_pol(spec_kind(xs, j), q)

def ev.links_pol(+a: NodeKind, +p: Nat, +xs: List<&2, Spec>, ls: List<&2, Link>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{Link{x, y}, t}:
      Bool.not(pol_eq(ev.end_pol(a, p, xs, x), ev.end_pol(a, p, xs, y))) && ev.links_pol(a, p, xs, t)

def ev.pol.r(r: Rule, +a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  match r:
    case RWire{+xs, ls}:
      Bool.not(pol_eq(port_pol(b, 0n), port_pol(a, p))) && ev.links_pol(a, p, xs, ls)
    case RStuck{}:
      True{}

# an event's eraser faces a port of the other polarity, and every link the
# event makes joins a positive port to a negative one (law
# events_polarized)
def ev_polarized(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  ev.pol.r(event(a, b, p), a, b, p)

def ports_of(xs: List<&2, Spec>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{Spec{k, s}, t}:
      Nat.add(arity(k), ports_of(t))

def ev.shr.r(r: Rule, +a: NodeKind, +b: NodeKind) -> Bool:
  match r:
    case RWire{xs, ls}:
      Nat.is_lt(ports_of(xs), Nat.add(arity(a), arity(b)))
    case RStuck{}:
      True{}

# an event leaves fewer ports than the node and the eraser had, so events
# end (law events_shrink)
def ev_shrinks(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  ev.shr.r(event(a, b, p), a, b)

def ev.m_eq(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case Some{x}:
      nat_eq(x, n)
    case None{}:
      False{}

def ev.side.c(a: NodeKind, +k: NodeKind, +p: Nat) -> Bool:
  match a:
    case KCopy{}:
      ev.m_eq(lf.dead_a(k), Nat.sub(p, 1n))
    case KMerge{}:
      ev.m_eq(lf.dead_b(k), Nat.add(p, 1n))
    case _:
      True{}

def ev.side.x(xs: List<&2, Spec>, +a: NodeKind, +p: Nat) -> Bool:
  match xs:
    case Con{Spec{k, s}, Nil{}}:
      ev.side.c(a, k, p)
    case _:
      True{}

def ev.side.r(r: Rule, +a: NodeKind, +p: Nat) -> Bool:
  match r:
    case RWire{xs, ls}:
      ev.side.x(xs, a, p)
    case RStuck{}:
      True{}

# the linear fan an event makes is the kind whose derived rules have the
# side erased that the event erased (law events_side)
def ev_side(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  ev.side.r(event(a, b, p), a, p)
