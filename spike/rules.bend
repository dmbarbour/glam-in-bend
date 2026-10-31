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
  KDCall{}

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
    case KDCall{} 0n:
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
# control's index) passed through the other, a control node. The laws'
# graphs compose them, each a source resolved against the nodes a rewrite
# took: SAp, a function applied to data; SLft, what x carries passed
# through control c; SSeg, units i to j - 1 of the run whose payload is
# c, unit brackets crossed in turn. No rule makes one (law
# rules_base_sources)
type Src is Data:
  SNone{}
  SPayA{}
  SPayB{}
  SApply{}
  SFanA{}
  SFanB{}
  SLiftA{}
  SLiftB{}
  SAp{f: Src, x: Src}
  SLft{x: Src, c: Src}
  SSeg{c: Src, i: Nat, j: Nat}

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

# node j's source s
def set_src(xs: List<&2, Spec>, j: Nat, +s: Src) -> List<&2, Spec>:
  match xs j:
    case Nil{} _:
      Nil{}
    case Con{Spec{k0, s0}, t} 0n:
      Con{Spec{k0, s}, t}
    case Con{h, t} 1n+i:
      Con{h, set_src(t, i, s)}

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

# Events (heap-strategies.erasure.events), above the normalizer that runs
# them: the table itself, with its laws below in "Events"

# a co-control's input an error value
def ev.in(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraP{}:
      match p:
        case 1n:
          RWire{[Spec{KEraP{}, SNone{}}], [lk(nw(0n, 0n), ex(0n))]}
        case _:
          RStuck{}
    case _:
      RStuck{}

# a control's output erased
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

# a call's result erased: a dead call, its function kept, stuck where a
# call is, so exact where the old event, an eraser of the input, was not
# (heap-strategies.erasure.deadcall)
def ev.call(b: NodeKind, p: Nat) -> Rule:
  match b:
    case KEraN{}:
      match p:
        case 1n:
          RWire{[Spec{KDCall{}, SPayA{}}], [lk(nw(0n, 0n), ex(0n))]}
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
    case KCall{}:
      ev.call(b, p)
    case KLift{}:
      ev.out(b, p)
    case KLiftC{}:
      ev.in(b, p)
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

def kind_n(k: NodeKind) -> Nat:
  match k:
    case KFree{}:
      0n
    case KFn{}:
      1n
    case KAp{}:
      2n
    case KCopy{}:
      3n
    case KMerge{}:
      4n
    case KData{}:
      5n
    case KEraN{}:
      6n
    case KEraP{}:
      7n
    case KRoot{}:
      8n
    case KCall{}:
      9n
    case KLift{}:
      10n
    case KLiftC{}:
      11n
    case KCopyL{}:
      12n
    case KCopyR{}:
      13n
    case KMergeL{}:
      14n
    case KMergeR{}:
      15n
    case KDCall{}:
      16n

# two sources the same, composed ones term by term
def src_eq(s: Src, u: Src) -> Bool:
  match s u:
    case SNone{} SNone{}:
      True{}
    case SPayA{} SPayA{}:
      True{}
    case SPayB{} SPayB{}:
      True{}
    case SApply{} SApply{}:
      True{}
    case SFanA{} SFanA{}:
      True{}
    case SFanB{} SFanB{}:
      True{}
    case SLiftA{} SLiftA{}:
      True{}
    case SLiftB{} SLiftB{}:
      True{}
    case SAp{f, x} SAp{g, y}:
      src_eq(f, g) && src_eq(x, y)
    case SLft{x, c} SLft{y, d}:
      src_eq(x, y) && src_eq(c, d)
    case SSeg{c, i, j} SSeg{d, k, l}:
      src_eq(c, d) && nat_eq(i, k) && nat_eq(j, l)
    case _ _:
      False{}

def specs_eq(xs: List<&2, Spec>, ys: List<&2, Spec>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{Spec{k, s}, xt} Con{Spec{l, u}, yt}:
      nat_eq(kind_n(k), kind_n(l)) && src_eq(s, u) && specs_eq(xt, yt)
    case _ _:
      False{}

def links_eq(xs: List<&2, Link>, ys: List<&2, Link>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{Link{a, b}, xt} Con{Link{c, d}, yt}:
      end_eq(a, c) && end_eq(b, d) && links_eq(xt, yt)
    case _ _:
      False{}

# two rules the same, node for node and link for link
def rule_eq(r: Rule, u: Rule) -> Bool:
  match r u:
    case RWire{xs, ls} RWire{ys, ms}:
      specs_eq(xs, ys) && links_eq(ls, ms)
    case RStuck{} RStuck{}:
      True{}
    case _ _:
      False{}

# a fused kind's full kind: a linear fan's fan, a dead call's call
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
    case KDCall{}:
      KCall{}
    case _:
      k

# Linear fans as their components (heap-strategies.fusions), for the
# normalizer, which applies the full fans' rules, and the laws

# a fused kind's dead port in its full kind's numbering (0 for none): a
# linear fan's erased side, a dead call's result (heap-strategies.erasure.
# deadcall); the eraser of a node of kind k's side; the full port a linear
# fan keeps, a dead call keeping none
def ex.dead(+k: NodeKind) -> Nat:
  match k:
    case KCopyL{}:
      2n
    case KCopyR{}:
      1n
    case KMergeL{}:
      2n
    case KMergeR{}:
      1n
    case KDCall{}:
      1n
    case _:
      0n

def ex.eraser(+k: NodeKind) -> NodeKind:
  match k:
    case KMergeL{}:
      KEraP{}
    case KMergeR{}:
      KEraP{}
    case KMerge{}:
      KEraP{}
    case KLiftC{}:
      KEraP{}
    case _:
      KEraN{}

def ex.kept(+k: NodeKind) -> Nat:
  match k:
    case KCopyR{}:
      2n
    case KMergeR{}:
      2n
    case _:
      1n

def fz.exp.mv(right: Bool, +ls: List<&2, Link>, +j: Nat) -> List<&2, Link>:
  match right:
    case True{}:
      lf.rename(ls, New{j, 1n}, New{j, 2n})
    case False{}:
      ls

# a linear fan in g as its components: node j's kind its full fan's, a
# kept port 1 moved to port 2 where the fan keeps its full port 2, an
# eraser at its dead port
def fz.exp.j(+d: Nat, +g: G, +j: Nat, +k: NodeKind) -> G:
  match g:
    case G{+xs, +ls}:
      G{List.append(&2, Spec, set_kind(xs, j, lf.full(k)), [Spec{ex.eraser(k), SNone{}}]),
        Con{Link{New{j, d}, New{List.length(&2, Spec, xs), 0n}}, fz.exp.mv(Nat.is_eq(d, 1n), ls, j)}}

def fz.exp.at(none: Bool, +g: G, +j: Nat, +k: NodeKind) -> G:
  match none:
    case True{}:
      g
    case False{}:
      fz.exp.j(ex.dead(k), g, j, k)

def fz.exp.go(m: Nat, +g: G, +j: Nat) -> G:
  match m:
    case 0n:
      g
    case 1n+r:
      fz.exp.go(r, fz.exp.at(Nat.is_eq(ex.dead(lf.kind(g, j)), 0n), g, j, lf.kind(g, j)), Nat.add(j, 1n))

# node j as its components, if a linear fan
def lf.expand.j(+g: G, +j: Nat) -> G:
  fz.exp.at(Nat.is_eq(ex.dead(lf.kind(g, j)), 0n), g, j, lf.kind(g, j))

# every linear fan of g as its components
def fz.expand(+g: G) -> G:
  fz.exp.go(lf.size(g), g, 0n)

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

# nodes a and b of g rewritten by r, if it rewrites
# Peers inside the redex (heap-strategies.fusions.loops), as the kernel's
# interpreter takes them (knet.bend's link_plain, link_pairs): external
# peer i that is a port of the redex itself, A's ports 1 and 2 standing
# for external peers 0 and 1, B's for 2 and 3, joins what the rule links
# to the two; a loop the rule's links and the redex's own close holds no
# node and vanishes (law rules_pairs_total: no longer chain arises)

def lf.partner.n(isa: Bool, isb: Bool, +q: Nat) -> Maybe<&2, Nat>:
  match isa isb:
    case True{} _:
      Some{Nat.sub(q, 1n)}
    case False{} True{}:
      Some{Nat.add(q, 1n)}
    case False{} False{}:
      None{}

def lf.partner.e(e: End, +a: Nat, +b: Nat) -> Maybe<&2, Nat>:
  match e:
    case New{+j, +q}:
      lf.partner.n(nat_eq(j, a), nat_eq(j, b), q)
    case Ext{i}:
      None{}

# the external peer a port of the redex is, for external peer i
def lf.partner(+ls: List<&2, Link>, +a: Nat, +b: Nat, +i: Nat) -> Maybe<&2, Nat>:
  lf.partner.e(lf.tr(ls, a, b, 0n, Ext{i}), a, b)

def lf.internal(+ls: List<&2, Link>, +a: Nat, +b: Nat, e: End) -> Bool:
  match e:
    case Ext{+i}:
      Maybe.is_some(&2, Nat, lf.partner(ls, a, b, i))
    case New{j, p}:
      False{}

def lf.plain.k(skip: Bool, +u: End, +v: End, rest: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat) -> List<&2, Link>:
  match skip:
    case True{}:
      rest
    case False{}:
      Con{Link{lf.tr(ls, a, b, n0, u), lf.tr(ls, a, b, n0, v)}, rest}

# the rule's links with no end inside the redex, in its order
def lf.plain(ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat) -> List<&2, Link>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Link{+u, +v}, t}:
      lf.plain.k(lf.internal(ls, a, b, u) || lf.internal(ls, a, b, v), u, v, lf.plain(t, ls, a, b, n0), ls, a, b, n0)

def lf.pair.ends(mu: Maybe<&2, End>, mv: Maybe<&2, End>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat) -> List<&2, Link>:
  match mu mv:
    case Some{+u} Some{+v}:
      lf.plain.k(lf.internal(ls, a, b, u) || lf.internal(ls, a, b, v), u, v, Nil{}, ls, a, b, n0)
    case _ _:
      Nil{}

def lf.pair.j(lt: Bool, +ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat, +i: Nat, +j: Nat) -> List<&2, Link>:
  match lt:
    case True{}:
      lf.pair.ends(lf.peer(ms, Ext{i}), lf.peer(ms, Ext{j}), ls, a, b, n0)
    case False{}:
      Nil{}

def lf.pair.i(m: Maybe<&2, Nat>, +ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat, +i: Nat) -> List<&2, Link>:
  match m:
    case Some{+j}:
      lf.pair.j(Nat.is_lt(i, j), ms, ls, a, b, n0, i, j)
    case None{}:
      Nil{}

# for each external peer i that is the redex's own port, partner of j > i,
# what the rule links to the two joined
def lf.pairs(k: Nat, +ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +n0: Nat, +i: Nat) -> List<&2, Link>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      List.append(&2, Link, lf.pair.i(lf.partner(ls, a, b, i), ms, ls, a, b, n0, i), lf.pairs(r, ms, ls, a, b, n0, Nat.add(i, 1n)))

# Control runs (heap-strategies.fusions.controls): a run of unit brackets
# stands for its units crossed in turn, so segments of one run, the first
# ending where the second begins, act as one (CT.run_splits)

def seg_join.ok(ok: Bool, +c: Src, +i: Nat, +l: Nat) -> Maybe<&2, Src>:
  match ok:
    case True{}:
      Some{SSeg{c, i, l}}
    case False{}:
      None{}

# segments d then c of one run, d ending where c begins: their join
def seg_join(d: Src, c: Src) -> Maybe<&2, Src>:
  match d c:
    case SSeg{+e, +i, +j} SSeg{+f, +k, +l}:
      seg_join.ok(src_eq(e, f) && nat_eq(j, k), e, i, l)
    case _ _:
      None{}

def lft.join(m: Maybe<&2, Src>, +y: Src, +d: Src, +c: Src) -> Src:
  match m:
    case Some{s}:
      SLft{y, s}
    case None{}:
      SLft{SLft{y, d}, c}

# x passed through control c: through consecutive segments of one run,
# through their join
def lf.lft(x: Src, +c: Src) -> Src:
  match x:
    case SLft{+y, +d}:
      lft.join(seg_join(d, c), y, d, c)
    case _:
      SLft{x, c}

# a new node's payload source, A's and B's those of the nodes taken (sa,
# sb): a payload or a fan's identity theirs, a function applied to data
# the term of the two, what one carries passed through the other, a
# control, the term of the two
def lf.res(s: Src, +sa: Src, +sb: Src) -> Src:
  match s:
    case SPayA{}:
      sa
    case SPayB{}:
      sb
    case SFanA{}:
      sa
    case SFanB{}:
      sb
    case SApply{}:
      SAp{sa, sb}
    case SLiftA{}:
      lf.lft(sa, sb)
    case SLiftB{}:
      lf.lft(sb, sa)
    case _:
      s

def lf.res.specs(ys: List<&2, Spec>, +sa: Src, +sb: Src) -> List<&2, Spec>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{Spec{k, s}, t}:
      Con{Spec{k, lf.res(s, sa, sb)}, lf.res.specs(t, sa, sb)}

# nodes a and b of g rewritten by r, if it rewrites: the rule's nodes,
# their payloads resolved against a's and b's; the rule's links with no
# end inside the redex, then those its own ports join
def lf.apply(r: Rule, g: G, +a: Nat, +b: Nat) -> Maybe<&2, G>:
  match r g:
    case RWire{ys, +ms} G{+xs, +ls}:
      Some{G{List.append(&2, Spec, set_kind(set_kind(xs, a, KFree{}), b, KFree{}), lf.res.specs(ys, spec_src(xs, a), spec_src(xs, b))),
        List.append(&2, Link, lf.unlink(lf.unlink(ls, a), b),
          List.append(&2, Link, lf.plain(ms, ls, a, b, List.length(&2, Spec, xs)), lf.pairs(4n, ms, ls, a, b, List.length(&2, Spec, xs), 0n)))}}
    case RStuck{} G{xs, ls}:
      None{}

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

def lf.other(p: Nat) -> Nat:
  match p:
    case 1n:
      2n
    case _:
      1n

# a new node's spec in an old one's slot, its source resolved as a
# rule's, A the old node, the eraser carrying none
def lf.put(+xs: List<&2, Spec>, +j: Nat, sp: Spec) -> List<&2, Spec>:
  match sp:
    case Spec{+k, s}:
      set_src(set_kind(xs, j, k), j, lf.res(s, spec_src(xs, j), SNone{}))

# the event's one new node placed in a's slot, b freed
def lf.place.one(ys: List<&2, Spec>, +xs: List<&2, Spec>, +a: Nat, +b: Nat) -> List<&2, Spec>:
  match ys:
    case Con{y0, t}:
      lf.put(set_kind(xs, b, KFree{}), a, y0)
    case Nil{}:
      set_kind(set_kind(xs, a, KFree{}), b, KFree{})

def lf.ev.end1(x: End, y: End) -> Bool:
  match x y:
    case New{j, q} Ext{i}:
      nat_eq(j, 0n)
    case Ext{i} New{j, q}:
      nat_eq(j, 0n)
    case _ _:
      False{}

def lf.ev.ext(ms: List<&2, Link>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{Link{x, y}, t}:
      lf.ev.end1(x, y) && lf.ev.ext(t)

# an event of one new node, linked only to external peers: in place, its
# links a's own, a port renamed where the node keeps it at another
def lf.ev.one(ys: List<&2, Spec>, ms: List<&2, Link>) -> Bool:
  match ys:
    case Con{y, t}:
      match t:
        case Nil{}:
          lf.ev.ext(ms)
        case _:
          False{}
    case Nil{}:
      False{}

# a's port that external peer i was the peer of
def lf.ev.port(+i: Nat, +p: Nat) -> Nat:
  match i:
    case 0n:
      0n
    case _:
      lf.other(p)

def lf.ev.ren1(x: End, y: End, +ls: List<&2, Link>, +a: Nat, +p: Nat) -> List<&2, Link>:
  match x y:
    case New{j, +q} Ext{+i}:
      lf.rename(ls, New{a, lf.ev.port(i, p)}, New{a, q})
    case Ext{+i} New{j, +q}:
      lf.rename(ls, New{a, lf.ev.port(i, p)}, New{a, q})
    case _ _:
      ls

def lf.ev.ren(ms: List<&2, Link>, +ls: List<&2, Link>, +a: Nat, +p: Nat) -> List<&2, Link>:
  match ms:
    case Nil{}:
      ls
    case Con{Link{x, y}, t}:
      lf.ev.ren(t, lf.ev.ren1(x, y, ls, a, p), a, p)

def lf.apply.ev.go(one: Bool, ys: List<&2, Spec>, ms: List<&2, Link>, +xs: List<&2, Spec>, +ls: List<&2, Link>, +a: Nat, +b: Nat, +p: Nat) -> Maybe<&2, G>:
  match one:
    case True{}:
      Some{G{lf.place.one(ys, xs, a, b), lf.ev.ren(ms, lf.unlink(ls, b), a, p)}}
    case False{}:
      None{}

# event r at port p of node a, eraser b, in place, its node in a's slot
# as the kernel places it (law kernel_events_in_step): the eraser's link
# gone, a's ports renamed where the node keeps them at others, as fans
# were marked linear. Every event is of one node linked only to external
# peers (law events_one_node); one of more would make no step here, the
# law failing first.
def lf.apply.ev(r: Rule, g: G, +a: Nat, +b: Nat, +p: Nat) -> Maybe<&2, G>:
  match r g:
    case RWire{+ys, +ms} G{+xs, +ls}:
      lf.apply.ev.go(lf.ev.one(ys, ms), ys, ms, xs, ls, a, b, p)
    case RStuck{} G{xs, ls}:
      None{}

def lf.rule.t.go(same: Bool, r: Rule) -> Maybe<&2, Rule>:
  match same:
    case True{}:
      Some{r}
    case False{}:
      None{}

# the rule for a pair of full kinds, where the payload test cannot change
# it: the normalizer knows no payload
def lf.rule.t(+x: NodeKind, +y: NodeKind) -> Maybe<&2, Rule>:
  lf.rule.t.go(rule_eq(rule.full(x, y, True{}), rule.full(x, y, False{})), rule.full(x, y, True{}))

# the pairs whose test compares their two payloads for equality, true of
# a payload met by itself: two fans' identities, an application's level
# and a function's, two controls' indexes (net.bend's rule_test)
def test_eq(a: NodeKind, b: NodeKind) -> Bool:
  match a b:
    case KCopy{} KMerge{}:
      True{}
    case KAp{} KFn{}:
      True{}
    case KLift{} KLiftC{}:
      True{}
    case _ _:
      False{}

def src_followed(s: Src) -> Bool:
  match s:
    case SNone{}:
      False{}
    case _:
      True{}

# A's and B's payloads known equal: one source, followed
def src_same(+sa: Src, +sb: Src) -> Bool:
  src_followed(sa) && src_eq(sa, sb)

def lf.rule.s(m: Maybe<&2, Rule>, same: Bool, +x: NodeKind, +y: NodeKind) -> Maybe<&2, Rule>:
  match m:
    case Some{r}:
      Some{r}
    case None{}:
      match same:
        case True{}:
          Some{rule.full(x, y, True{})}
        case False{}:
          None{}

# the rule for x meeting y, their sources sx and sy: where the payload
# test cannot change it, or where it compares the payloads and they are
# one, the test passing; else none, the normalizer knowing no more
def lf.rule.k(+x: NodeKind, +y: NodeKind, +sx: Src, +sy: Src) -> Maybe<&2, Rule>:
  lf.rule.s(lf.rule.t(x, y), test_eq(x, y) && src_same(sx, sy), x, y)

def lf.pair.r(m: Maybe<&2, Rule>, +g: G, +x: Nat, +y: Nat) -> Maybe<&2, G>:
  match m:
    case Some{r}:
      lf.apply(r, g, x, y)
    case None{}:
      None{}

def lf.pair.k(+g: G, +x: Nat, +y: Nat) -> Maybe<&2, G>:
  match g:
    case G{+xs, +ls}:
      lf.pair.r(lf.rule.k(lf.kind(G{xs, ls}, x), lf.kind(G{xs, ls}, y), spec_src(xs, x), spec_src(xs, y)), G{xs, ls}, x, y)

def lf.pair.o(neg: Bool, +g: G, +x: Nat, +y: Nat) -> Maybe<&2, G>:
  match neg:
    case True{}:
      lf.pair.k(g, x, y)
    case False{}:
      lf.pair.k(g, y, x)

# nodes x and y, their principals facing, rewritten by the full fans'
# table, linear fans expanded first, x's principal negative or y's
def lf.pair(+g: G, +x: Nat, +y: Nat) -> Maybe<&2, G>:
  lf.pair.o(pol_eq(port_pol(lf.kind(lf.expand.j(lf.expand.j(g, x), y), x), 0n), Neg{}), lf.expand.j(lf.expand.j(g, x), y), x, y)

# an eraser e facing port p of node j: a rule where p is the principal,
# an event of the table's (R.event) where it is an auxiliary one
def lf.at_j.ev(+p: Nat, ke: NodeKind, kj: NodeKind, +g: G, +e: Nat, +j: Nat) -> Maybe<&2, G>:
  lf.apply.ev(event(kj, ke, p), g, j, e, p)

def lf.at_j(p: Nat, ke: NodeKind, kj: NodeKind, +g: G, +e: Nat, +j: Nat) -> Maybe<&2, G>:
  match p:
    case 0n:
      lf.pair(g, e, j)
    case 1n+q:
      lf.at_j.ev(1n+q, ke, kj, g, e, j)

# eraser e of kind ke facing end x: an erasure where x is a principal
# port, an event where it is an auxiliary one
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

# node j's principal facing another node's: their rule
def lf.at_p(+g: G, +j: Nat, x: Maybe<&2, End>) -> Maybe<&2, G>:
  match x:
    case Some{e}:
      match e:
        case New{+k, p}:
          match p:
            case 0n:
              lf.pair(g, j, k)
            case _:
              None{}
        case Ext{i}:
          None{}
    case None{}:
      None{}

def lf.fuse.ls(m: Maybe<&2, End>, ls: List<&2, Link>, +j: Nat) -> List<&2, Link>:
  match m:
    case Some{e}:
      Con{Link{New{j, 1n}, e}, ls}
    case None{}:
      ls

def lf.fuse.s(m: Maybe<&2, Src>, +g: G, +j: Nat, +y: Nat) -> Maybe<&2, G>:
  match m g:
    case Some{s} G{+xs, +ls}:
      Some{G{set_kind(set_src(xs, j, s), y, KFree{}), lf.fuse.ls(lf.peer(ls, New{y, 1n}), lf.unlink(ls, y), j)}}
    case None{} G{xs, ls}:
      None{}

def lf.fuse.k(same: Bool, +g: G, +j: Nat, +y: Nat) -> Maybe<&2, G>:
  match same g:
    case True{} G{+xs, +ls}:
      lf.fuse.s(seg_join(spec_src(xs, j), spec_src(xs, y)), G{xs, ls}, j, y)
    case False{} G{xs, ls}:
      None{}

def lf.fuse.y(e: Maybe<&2, End>, +g: G, +j: Nat) -> Maybe<&2, G>:
  match e:
    case Some{x}:
      match x:
        case New{+y, p}:
          match p:
            case 0n:
              lf.fuse.k(nat_eq(kind_n(lf.kind(g, j)), kind_n(lf.kind(g, y))) && Bool.not(nat_eq(j, y)), g, j, y)
            case _:
              None{}
        case Ext{i}:
          None{}
    case None{}:
      None{}

# control j and a control of its kind whose principal its auxiliary
# feeds, segments of one run, the first ending where the second begins:
# one control in j's slot, its auxiliary facing the second's peer there
# (V.compose's rule, which the interpreters apply after each rewrite)
def lf.fuse(+g: G, +j: Nat) -> Maybe<&2, G>:
  match g:
    case G{+xs, +ls}:
      lf.fuse.y(lf.peer(ls, New{j, 1n}), G{xs, ls}, j)

def lf.at_c(m: Maybe<&2, G>, +g: G, +j: Nat) -> Maybe<&2, G>:
  match m:
    case Some{h}:
      Some{h}
    case None{}:
      lf.fuse(g, j)

def lf.try.k(k: NodeKind, +g: G, +j: Nat, x: Maybe<&2, End>) -> Maybe<&2, G>:
  match k:
    case KEraN{}:
      lf.at_e(KEraN{}, g, j, x)
    case KEraP{}:
      lf.at_e(KEraP{}, g, j, x)
    case KFree{}:
      None{}
    case KLift{}:
      lf.at_c(lf.at_p(g, j, x), g, j)
    case KLiftC{}:
      lf.at_c(lf.at_p(g, j, x), g, j)
    case _:
      lf.at_p(g, j, x)

# what node j can run: an eraser, its erasure or event; another node
# whose principal faces a principal, their rule
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

# where the dead side was, as the full rule numbers its external peers:
# A's, a copy's erased output or a dead call's result; B's, a merge's
# erased input
def lf.dead_a(k: NodeKind) -> Maybe<&2, Nat>:
  match k:
    case KCopyL{}:
      Some{1n}
    case KCopyR{}:
      Some{0n}
    case KDCall{}:
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
  lf.fin(lf.norm(64n, lf.scan(lf.size(g), lf.try(g, 0n), g, 0n), g), lf.right_a(a), lf.right_b(b))

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
# as rule.full says: a full kind's rule, or a fused one's derived from it
# (a linear fan's, a dead call's);
# a kind whose principal is positive is never A, and stuck as one
def rule(a: NodeKind, b: NodeKind, t: Bool) -> Rule:
  match a:
    case KDCall{}:
      lf.derive(KDCall{}, b, t)
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

# the net's header counts events a word a kind, for the codes below 16
# (kprim.bend's at_evk): a kind coded past them makes none
def ev_header(+a: NodeKind, b: NodeKind, p: Nat) -> Bool:
  Nat.is_lt(kind_n(a), 16n) || is_stuck(event(a, b, p))

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

# What the normalizer takes for granted (heap-strategies.fusions.assume)

# no eraser's rule depends on the payload test, so the normalizer, which
# knows no payload, applies every erasure (law erasers_untested)
def erasers_untested(+k: NodeKind) -> Bool:
  rule_eq(rule.full(KEraN{}, k, True{}), rule.full(KEraN{}, k, False{})) &&
    rule_eq(rule.full(k, KEraP{}, True{}), rule.full(k, KEraP{}, False{}))

def self.end(x: End, y: End) -> Bool:
  match x y:
    case New{+i, p} New{+j, q}:
      nat_eq(i, j)
    case _ _:
      False{}

def self.links(ls: List<&2, Link>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{Link{x, y}, t}:
      self.end(x, y) || self.links(t)

def no_self.r(r: Rule) -> Bool:
  match r:
    case RWire{xs, ls}:
      Bool.not(self.links(ls))
    case RStuck{}:
      True{}

# no rule links two ports of one of its new nodes: rewriting never makes a
# node face itself of its own (law rules_no_self_links)
def no_self_links(+a: NodeKind, +b: NodeKind, +t: Bool) -> Bool:
  no_self.r(rule(a, b, t))

def base.src(s: Src) -> Bool:
  match s:
    case SAp{f, x}:
      False{}
    case SLft{x, c}:
      False{}
    case SSeg{c, i, j}:
      False{}
    case _:
      True{}

def base.specs(xs: List<&2, Spec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Spec{k, s}, t}:
      base.src(s) && base.specs(t)

def base.r(r: Rule) -> Bool:
  match r:
    case RWire{xs, ls}:
      base.specs(xs)
    case RStuck{}:
      True{}

# every rule's new nodes take their payloads from A's and B's as the
# kernel does, none a composed source, derived rules too (law
# rules_base_sources)
def base_sources(+a: NodeKind, +b: NodeKind, +t: Bool) -> Bool:
  base.r(rule(a, b, t))

# every event's new node too (law events_base_sources)
def ev_base_sources(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  base.r(event(a, b, p))

def ev_one.r(r: Rule) -> Bool:
  match r:
    case RWire{ys, ms}:
      lf.ev.one(ys, ms)
    case RStuck{}:
      True{}

# every event makes one node, linked only to external peers, which the
# normalizer applies in place (law events_one_node)
def ev_one_node(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  ev_one.r(event(a, b, p))

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
# changes its kind in place. A control whose output is erased becomes an
# eraser facing what it took in, and a co-control whose input is an error
# value, an error value where its output goes; a copy one of whose
# outputs is erased, a linear copy keeping the other, and a linear copy
# whose output is erased, an eraser; a merge one of whose inputs is an
# error value, a linear merge keeping the other, and a linear merge whose
# input is one, an error value. Each preserves meaning exactly
# (heap-strategies.erasure.kernel.exact; law events_erase_exact). No
# event for an application whose result is erased: erasing its function
# would not apply it, and applying it binds the function's variable,
# which a net may use outside the function's body (the maintainer,
# 2026-10-30: dropped, the rule kept for where it is exact). None for a
# call whose output is erased: against a function its rule is stuck, and
# stuck is not erased (the maintainer, 2026-10-30).

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

def ev.last.k(k: NodeKind, +a: NodeKind) -> Bool:
  match k:
    case KEraN{}:
      nat_eq(arity(a), 2n)
    case KEraP{}:
      nat_eq(arity(a), 2n)
    case _:
      True{}

def ev.last.r(r: Rule, +a: NodeKind) -> Bool:
  match r:
    case RWire{xs, ls}:
      match xs:
        case Con{Spec{+k, s}, t}:
          ev.last.k(k, a)
        case Nil{}:
          True{}
    case RStuck{}:
      True{}

# an event that makes its node an eraser erased the node's last auxiliary
# port: the node had two ports (law events_erase_last)
def ev_last(+a: NodeKind, +b: NodeKind, +p: Nat) -> Bool:
  ev.last.r(event(a, b, p), a)

# Fusions behave as their components
# ----------------------------------
#
# heap-strategies.erasure.kernel.exact (the maintainer, 2026-10-30): a
# fused node, or a pattern an event rewrites into one node, behaves as
# its components against whatever its principal meets. Both are stuck
# there, or neither, and then what they leave is the same graph: linear
# fans expanded into their components, both normalized by the
# derivation's normalizer (lf.norm: erasures and the events, each itself
# checked here, so equal up to them), compared in a canonical order. A
# linear fan's components are its full fan and an eraser at its dead
# side (law linear_as_components); an event's, its node and the eraser at
# the port it erases, against the node the event makes (law
# events_as_components). The interface is no partner: no rule rewrites
# it, and a superposition and an error value read alike there.

# a graph built up, node by node
type XB is Data:
  XB{xs: List<&2, Spec>, ls: List<&2, Link>}

def xb.add.s(+b: XB, +k: NodeKind, +s: Src) -> XB:
  match b:
    case XB{+xs, +ls}:
      XB{List.append(&2, Spec, xs, [Spec{k, s}]), ls}

def xb.add(+b: XB, +k: NodeKind) -> XB:
  xb.add.s(b, k, SNone{})

# a node of kind k, its payload source s if it carries one: data, a
# call's function, a level, a fan's identity, a control's index; an
# eraser or the root none
def xb.add.p(+b: XB, k: NodeKind, +s: Src) -> XB:
  match k:
    case KEraN{}:
      xb.add(b, KEraN{})
    case KEraP{}:
      xb.add(b, KEraP{})
    case KRoot{}:
      xb.add(b, KRoot{})
    case KFree{}:
      xb.add(b, KFree{})
    case _:
      xb.add.s(b, k, s)

def xb.link(+b: XB, +u: End, +v: End) -> XB:
  match b:
    case XB{+xs, +ls}:
      XB{xs, Con{Link{u, v}, ls}}

def xb.size(+b: XB) -> Nat:
  match b:
    case XB{+xs, +ls}:
      List.length(&2, Spec, xs)

def xb.g(+b: XB) -> G:
  match b:
    case XB{+xs, +ls}:
      G{xs, ls}

# node n's auxiliary port q, its full kind's numbering, linked: an eraser
# at a dead port (components), else external peer base + q - 1
def xb.port(dead: Bool, +b: XB, +n: Nat, +k: NodeKind, +q: Nat, +base: Nat) -> XB:
  match dead:
    case True{}:
      xb.link(xb.add(b, ex.eraser(k)), New{n, q}, New{xb.size(b), 0n})
    case False{}:
      xb.link(b, New{n, q}, Ext{Nat.sub(Nat.add(base, q), 1n)})

def xb.ports(m: Nat, +b: XB, +n: Nat, +k: NodeKind, +q: Nat, +base: Nat) -> XB:
  match m:
    case 0n:
      b
    case 1n+r:
      xb.ports(r, xb.port(Nat.is_eq(q, ex.dead(k)), b, n, k, q, base), n, k, Nat.add(q, 1n), base)

# node n of kind k as its components: its full kind's auxiliary ports,
# the dead one erased, the rest external peers from base
def xb.comp(+b: XB, +n: Nat, +k: NodeKind, +base: Nat) -> XB:
  xb.ports(Nat.sub(arity(lf.full(k)), 1n), b, n, k, 1n, base)

def xb.fused.kept(kept: Bool, +b: XB, +n: Nat, +k: NodeKind, +base: Nat) -> XB:
  match kept:
    case True{}:
      xb.link(b, New{n, 1n}, Ext{Nat.sub(Nat.add(base, ex.kept(k)), 1n)})
    case False{}:
      b

def xb.fused.lin(lin: Bool, +b: XB, +n: Nat, +k: NodeKind, +base: Nat) -> XB:
  match lin:
    case True{}:
      xb.fused.kept(Nat.is_gt(arity(k), 1n), b, n, k, base)
    case False{}:
      xb.comp(b, n, k, base)

# node n of kind k as it is, a linear fan's one auxiliary port the external
# peer its full kind's kept port would have, a dead call's none
def xb.fused(+b: XB, +n: Nat, +k: NodeKind, +base: Nat) -> XB:
  xb.fused.lin(Bool.not(Nat.is_eq(ex.dead(k), 0n)), b, n, k, base)

# Canonical order: the nodes reached from external peers 0 to 3, breadth
# first, each node's ports in order; a node's place in the order names it

def fz.idx.hit(hit: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      rest

# j's place in ns, counting from i
def fz.idx(ns: List<&2, Nat>, +j: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case Con{+n, t}:
      fz.idx.hit(Nat.is_eq(n, j), i, fz.idx(t, j, Nat.add(i, 1n)))

def fz.seen(+ns: List<&2, Nat>, +j: Nat) -> Bool:
  Maybe.is_some(&2, Nat, fz.idx(ns, j, 0n))

def fz.see.j(seen: Bool, +ns: List<&2, Nat>, +j: Nat) -> List<&2, Nat>:
  match seen:
    case True{}:
      ns
    case False{}:
      List.append(&2, Nat, ns, [j])

# the node at end m, if new to ns, added
def fz.see(m: Maybe<&2, End>, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{e}:
      match e:
        case New{+j, p}:
          fz.see.j(fz.seen(ns, j), ns, j)
        case Ext{i}:
          ns
    case None{}:
      ns

# node j's ports from q, m of them, their nodes seen
def fz.ports(m: Nat, +ls: List<&2, Link>, +j: Nat, +q: Nat, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case 0n:
      ns
    case 1n+r:
      fz.ports(r, ls, j, Nat.add(q, 1n), fz.see(lf.peer(ls, New{j, q}), ns))

def fz.nth(ns: List<&2, Nat>, i: Nat) -> Nat:
  match ns i:
    case Con{+n, t} 0n:
      n
    case Con{n, t} 1n+r:
      fz.nth(t, r)
    case Nil{} _:
      0n

# the node at place i's ports, their nodes seen, if there is one
def fz.order.go(more: Bool, +g: G, +i: Nat, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match more:
    case False{}:
      ns
    case True{}:
      match g:
        case G{+xs, +ls}:
          fz.ports(arity(lf.kind(G{xs, ls}, fz.nth(ns, i))), ls, fz.nth(ns, i), 0n, ns)

# the order: from the node at place i on, k steps of fuel
def fz.order(k: Nat, +g: G, +i: Nat, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      ns
    case 1n+r:
      fz.order(r, g, Nat.add(i, 1n), fz.order.go(Nat.is_lt(i, List.length(&2, Nat, ns)), g, i, ns))

# an end as a number: none 0, external peer i 1 + i, port p of the node at
# place i 10 + 4i + p
def fz.end(m: Maybe<&2, End>, +ns: List<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{e}:
      match e:
        case Ext{+i}:
          Nat.add(1n, i)
        case New{+j, +p}:
          Nat.add(Nat.add(10n, Nat.mul(4n, Maybe.default(&2, Nat, fz.idx(ns, j, 0n), 0n))), p)

def fz.ends(m: Nat, +ls: List<&2, Link>, +j: Nat, +q: Nat, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case 0n:
      Nil{}
    case 1n+r:
      Con{fz.end(lf.peer(ls, New{j, q}), ns), fz.ends(r, ls, j, Nat.add(q, 1n), ns)}

# each node in order: its kind, then its ports' peers
# a node's payload source: the pattern node's (1) or its partner's (2), a
# function applied to data (3, then each), one passed through a control
# (5, then each); a rule's unresolved, 4 and 6 to 9; none 0
def fz.src(s: Src) -> List<&2, Nat>:
  match s:
    case SNone{}:
      [0n]
    case SPayA{}:
      [1n]
    case SPayB{}:
      [2n]
    case SAp{f, x}:
      Con{3n, List.append(&2, Nat, fz.src(f), fz.src(x))}
    case SApply{}:
      [4n]
    case SLft{x, c}:
      Con{5n, List.append(&2, Nat, fz.src(x), fz.src(c))}
    case SSeg{c, i, j}:
      Con{10n, Con{i, Con{j, fz.src(c)}}}
    case SFanA{}:
      [6n]
    case SFanB{}:
      [7n]
    case SLiftA{}:
      [8n]
    case SLiftB{}:
      [9n]

def fz.nodes(rest: List<&2, Nat>, +g: G, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match rest:
    case Nil{}:
      Nil{}
    case Con{+j, t}:
      match g:
        case G{+xs, +ls}:
          Con{kind_n(lf.kind(G{xs, ls}, j)), List.append(&2, Nat, fz.src(spec_src(xs, j)), List.append(&2, Nat, fz.ends(arity(lf.kind(G{xs, ls}, j)), ls, j, 0n, ns), fz.nodes(t, G{xs, ls}, ns)))}

def fz.live(xs: List<&2, Spec>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{Spec{k, s}, t}:
      match k:
        case KFree{}:
          fz.live(t)
        case _:
          Nat.add(1n, fz.live(t))

def fz.canon.o(+g: G, +ns: List<&2, Nat>) -> List<&2, Nat>:
  match g:
    case G{+xs, +ls}:
      List.append(&2, Nat, [fz.end(lf.peer(ls, Ext{0n}), ns), fz.end(lf.peer(ls, Ext{1n}), ns),
          fz.end(lf.peer(ls, Ext{2n}), ns), fz.end(lf.peer(ls, Ext{3n}), ns), Nat.sub(fz.live(xs), List.length(&2, Nat, ns))],
        fz.nodes(ns, G{xs, ls}, ns))

# g in canonical order: what external peers 0 to 3 face, how many live
# nodes no external peer reaches, then each node reached, in order
def fz.canon(+g: G) -> List<&2, Nat>:
  match g:
    case G{+xs, +ls}:
      fz.canon.o(G{xs, ls}, fz.order(lf.size(G{xs, ls}), G{xs, ls}, 0n,
        fz.see(lf.peer(ls, Ext{3n}), fz.see(lf.peer(ls, Ext{2n}), fz.see(lf.peer(ls, Ext{1n}), fz.see(lf.peer(ls, Ext{0n}), Nil{}))))))

def fz.after.n(m: Maybe<&2, G>) -> List<&2, Nat>:
  match m:
    case Some{g}:
      fz.canon(g)
    case None{}:
      [999n]

# what a rewrite leaves: none where the rule is stuck, else the graph
# expanded, normalized, in canonical order
def fz.after(m: Maybe<&2, G>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{+g}:
      Some{fz.after.n(lf.norm(64n, Some{fz.expand(g)}, fz.expand(g)))}

def ex.eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+x, xt} Con{+y, yt}:
      Nat.is_eq(x, y) && ex.eq(xt, yt)
    case _ _:
      False{}

def fz.same(a: Maybe<&2, List<&2, Nat>>, b: Maybe<&2, List<&2, Nat>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      ex.eq(x, y)
    case _ _:
      False{}

# the rule table, or its full fans' (rule.full) for components
def fz.rule(full: Bool, +a: NodeKind, +b: NodeKind, +t: Bool) -> Rule:
  match full:
    case True{}:
      rule.full(a, b, t)
    case False{}:
      rule(a, b, t)

# nodes 0 (kind x) and 1 (kind y) of g rewritten, oriented by x's
# principal
def ex.apply.r(neg: Bool, +g: G, +x: NodeKind, +y: NodeKind, +t: Bool, +full: Bool) -> Maybe<&2, G>:
  match neg:
    case True{}:
      lf.apply(fz.rule(full, x, y, t), g, 0n, 1n)
    case False{}:
      lf.apply(fz.rule(full, y, x, t), g, 1n, 0n)

def fz.run(+x: NodeKind, +y: NodeKind, +t: Bool, +full: Bool, +g: G) -> Maybe<&2, List<&2, Nat>>:
  fz.after(ex.apply.r(pol_eq(port_pol(x, 0n), Neg{}), g, x, y, t, full))

def ex.partner(v: NodeKind) -> Bool:
  match v:
    case KRoot{}:
      False{}
    case KFree{}:
      False{}
    case _:
      True{}

def fz.meets(+a: NodeKind, +v: NodeKind) -> Bool:
  Bool.not(pol_eq(port_pol(a, 0n), port_pol(v, 0n))) && ex.partner(v)

def fz.go(go: Bool, +r: Bool) -> Bool:
  match go:
    case True{}:
      r
    case False{}:
      True{}

# a linear fan f facing v (as it is) against f's components facing v's
def fz_linear.cmp(+f: NodeKind, +v: NodeKind, +t: Bool) -> Bool:
  fz.same(
    fz.run(f, v, t, False{}, xb.g(xb.fused(xb.fused(xb.link(xb.add.p(xb.add.p(XB{[], []}, f, SPayA{}), v, SPayB{}), New{0n, 0n}, New{1n, 0n}), 0n, f, 0n), 1n, v, 2n))),
    fz.run(lf.full(f), lf.full(v), t, True{}, xb.g(xb.comp(xb.comp(xb.link(xb.add.p(xb.add.p(XB{[], []}, lf.full(f), SPayA{}), lf.full(v), SPayB{}), New{0n, 0n}, New{1n, 0n}), 0n, f, 0n), 1n, v, 2n))))

# a linear fan behaves as its components against any partner (law
# linear_as_components)
def fz_linear(+f: NodeKind, +v: NodeKind, +t: Bool) -> Bool:
  fz.go(Bool.not(Nat.is_eq(ex.dead(f), 0n)) && fz.meets(f, v), fz_linear.cmp(f, v, t))

def ex.first(r: Rule) -> NodeKind:
  match r:
    case RWire{xs, ls}:
      match xs:
        case Con{Spec{+k, s}, t}:
          k
        case Nil{}:
          KFree{}
    case RStuck{}:
      KFree{}

# the source of a rule's first node
def ex.first.s(r: Rule) -> Src:
  match r:
    case RWire{xs, ls}:
      match xs:
        case Con{Spec{k, +s}, t}:
          s
        case Nil{}:
          SNone{}
    case RStuck{}:
      SNone{}

def fz.evport.go(full: Bool, +a: NodeKind, +p: Nat) -> Nat:
  match full:
    case True{}:
      p
    case False{}:
      ex.kept(a)

# the full port an event at port p of a node of kind a erases: a linear
# fan's kept one
def fz.evport(+a: NodeKind, +p: Nat) -> Nat:
  fz.evport.go(Nat.is_eq(ex.dead(a), 0n), a, p)

def fz.pat.at(here: Bool, +b: XB, +a: NodeKind, +q: Nat) -> XB:
  match here:
    case True{}:
      xb.link(b, New{0n, q}, New{2n, 0n})
    case False{}:
      xb.port(Nat.is_eq(q, ex.dead(a)), b, 0n, a, q, 0n)

# a's ports from q: its dead one erased, port p to the eraser at node 2,
# the rest external peers
def fz.pat.q(m: Nat, +b: XB, +a: NodeKind, +p: Nat, +q: Nat) -> XB:
  match m:
    case 0n:
      b
    case 1n+r:
      fz.pat.q(r, fz.pat.at(Nat.is_eq(q, p), b, a, q), a, p, Nat.add(q, 1n))

def fz.pat.a(+b: XB, +a: NodeKind, +p: Nat) -> XB:
  fz.pat.q(Nat.sub(arity(lf.full(a)), 1n), b, a, p, 1n)

# the pattern: a's components facing v's, a's port p (full numbering)
# erased by an eraser of kind b at node 2
def fz.pattern(+a: NodeKind, +b: NodeKind, +p: Nat, +v: NodeKind) -> G:
  xb.g(xb.comp(fz.pat.a(xb.link(xb.add(xb.add.p(xb.add.p(XB{[], []}, lf.full(a), SPayA{}), lf.full(v), SPayB{}), b), New{0n, 0n}, New{1n, 0n}), a, p), 1n, v, 2n))

def fz.res.go(none: Bool, +b: XB, +e: NodeKind) -> XB:
  match none:
    case True{}:
      b
    case False{}:
      xb.comp(b, 0n, e, 0n)

# the event's result, its node of kind e as its components: a linear fan
# its kept port the pattern's port not erased, an eraser none; its source
# s as the event gives it, A's the pattern node's
def fz.result(+e: NodeKind, +s: Src, +v: NodeKind) -> G:
  xb.g(xb.comp(fz.res.go(Nat.is_eq(ex.dead(e), 0n), xb.link(xb.add.p(xb.add.p(XB{[], []}, lf.full(e), lf.res(s, SPayA{}, SNone{})), lf.full(v), SPayB{}), New{0n, 0n}, New{1n, 0n}), e), 1n, v, 2n))

def fz_event.cmp(+a: NodeKind, +b: NodeKind, +p: Nat, +e: NodeKind, +s: Src, +v: NodeKind, +t: Bool) -> Bool:
  fz.same(fz.run(lf.full(a), lf.full(v), t, True{}, fz.pattern(a, b, fz.evport(a, p), v)),
    fz.run(lf.full(e), lf.full(v), t, True{}, fz.result(e, s, v)))

# an event's pattern behaves as the node it makes, against any partner
# (law events_as_components): the event at port p of a node of kind a,
# by its kind's eraser
def fz_event(+a: NodeKind, +p: Nat, +v: NodeKind, +t: Bool) -> Bool:
  fz.go(Bool.not(is_stuck(event(a, ex.eraser(a), p))) && fz.meets(a, v),
    fz_event.cmp(a, ex.eraser(a), p, ex.first(event(a, ex.eraser(a), p)), ex.first.s(event(a, ex.eraser(a), p)), v, t))

# Control runs: a run as its units
# --------------------------------
#
# heap-strategies.fusions.controls. A control facing a partner, as one
# run of two units, and as the units in series, the first at the
# principal, each one's auxiliary feeding the next one's principal, both
# kinds alike (V.compose: the first is the one whose auxiliary feeds the
# other). Two units stand for any split, the normalizer reading segment
# bounds only to join them (CT.run_splits holds the arithmetic). A
# partner that is itself a control facing it is peeling's case, its
# test on the two payloads' values.

def fz.ctl(k: NodeKind) -> Bool:
  match k:
    case KLift{}:
      True{}
    case KLiftC{}:
      True{}
    case _:
      False{}

def fz.run.g(+k: NodeKind, +v: NodeKind) -> G:
  xb.g(xb.fused(xb.link(xb.link(xb.add.p(xb.add.s(XB{[], []}, k, SSeg{SPayA{}, 0n, 2n}), v, SPayB{}), New{0n, 0n}, New{1n, 0n}), New{0n, 1n}, Ext{0n}), 1n, v, 2n))

def fz.units.g(+k: NodeKind, +v: NodeKind) -> G:
  xb.g(xb.fused(xb.link(xb.link(xb.link(xb.add.s(xb.add.p(xb.add.s(XB{[], []}, k, SSeg{SPayA{}, 0n, 1n}), v, SPayB{}), k, SSeg{SPayA{}, 1n, 2n}),
    New{0n, 0n}, New{1n, 0n}), New{0n, 1n}, New{2n, 0n}), New{2n, 1n}, Ext{0n}), 1n, v, 2n))

def fz_run.cmp(+k: NodeKind, +v: NodeKind, +t: Bool) -> Bool:
  fz.same(fz.run(k, v, t, False{}, fz.run.g(k, v)), fz.run(k, v, t, False{}, fz.units.g(k, v)))

# a run facing any partner but a control is stuck where its units are,
# and otherwise leaves what they leave, both normalized, controls fused
# (law runs_as_units)
def fz_runs(+k: NodeKind, +v: NodeKind, +t: Bool) -> Bool:
  fz.go(fz.ctl(k) && Bool.not(pol_eq(port_pol(k, 0n), port_pol(v, 0n))) && Bool.not(fz.ctl(v)) && Bool.not(is_free_k(v)), fz_run.cmp(k, v, t))

# Loops: a node's port facing its own other port
# -----------------------------------------------
#
# heap-strategies.fusions.loops (the maintainer, 2026-10-30). Principal to
# auxiliary is a vicious circle on any node: its principal faces no other
# node's, so it never interacts. Auxiliary to auxiliary, polarity allows
# only on a function, its body its variable, the identity, or on an
# application, its result its argument, which applying its function
# knots into the function's body feeding its variable: observed only
# where that variable is, which may be outside the body
# (`ap-self-extruded` in the library). A fan's two outputs, or two
# inputs, share a polarity. A linear fan keeps its full fan's polarities
# at the ports it keeps, so its loops are its components'.

def is_bind(k: NodeKind) -> Bool:
  match k:
    case KFn{}:
      True{}
    case KAp{}:
      True{}
    case _:
      False{}

# auxiliary ports of opposite polarity, which a loop may join, only on a
# function or an application (law aux_loops)
def loops_aux(+k: NodeKind) -> Bool:
  Bool.not(nat_eq(arity(k), 3n) && Bool.not(pol_eq(port_pol(k, 1n), port_pol(k, 2n)))) || is_bind(k)

def fused_pol.aux(full: Bool, +k: NodeKind) -> Bool:
  match full:
    case True{}:
      True{}
    case False{}:
      pol_eq(port_pol(k, 1n), port_pol(lf.full(k), ex.kept(k)))

# a linear fan's ports have its full fan's polarities at the ports it
# keeps (law fused_polarity)
def fused_pol(+k: NodeKind) -> Bool:
  pol_eq(port_pol(k, 0n), port_pol(lf.full(k), 0n)) && fused_pol.aux(Nat.is_eq(ex.dead(k), 0n), k)

def loop.ap(l: Bool) -> List<&2, Link>:
  match l:
    case True{}:
      [Link{New{0n, 1n}, New{0n, 2n}}]
    case False{}:
      [Link{New{0n, 1n}, Ext{0n}}, Link{New{0n, 2n}, Ext{1n}}]

def loop.fn(l: Bool) -> List<&2, Link>:
  match l:
    case True{}:
      [Link{New{1n, 1n}, New{1n, 2n}}]
    case False{}:
      [Link{New{1n, 1n}, Ext{2n}}, Link{New{1n, 2n}, Ext{3n}}]

# an application (node 0) meeting a function (node 1): its argument and
# result external peers 0 and 1, or joined; the function's body and
# variable 2 and 3, or joined
def loop.g(+ap: Bool, +fn: Bool) -> G:
  G{[Spec{KAp{}, SNone{}}, Spec{KFn{}, SNone{}}], Con{Link{New{0n, 0n}, New{1n, 0n}}, List.append(&2, Link, loop.ap(ap), loop.fn(fn))}}

def loop.after(m: Maybe<&2, G>) -> List<&2, Nat>:
  match m:
    case Some{g}:
      fz.canon(g)
    case None{}:
      [999n]

def loop.after.n(m: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match m:
    case Some{xs}:
      xs
    case None{}:
      [999n]

def loop.beta(+ap: Bool, +fn: Bool) -> List<&2, Nat>:
  loop.after(lf.apply(rule(KAp{}, KFn{}, True{}), loop.g(ap, fn), 0n, 1n))

# beta with loops: a function whose body is its variable is the identity,
# the argument's peer joined to the result's; an application whose result
# is its argument knots the function, its body's peer joined to its
# variable's; both, nothing left; neither, beta (law beta_loops). In
# canonical order, what external peers 0 to 3 face (none 0, peer i 1 + i)
# and the nodes left.
def beta_loops() -> Bool:
  ex.eq(loop.beta(False{}, True{}), [2n, 1n, 0n, 0n, 0n]) && ex.eq(loop.beta(True{}, False{}), [0n, 0n, 4n, 3n, 0n]) &&
    ex.eq(loop.beta(True{}, True{}), [0n, 0n, 0n, 0n, 0n]) && ex.eq(loop.beta(False{}, False{}), [4n, 3n, 2n, 1n, 0n])

# a copy (node 0) meeting the identity function (node 1), its outputs
# external peers 0 and 1
def loop.copy.g() -> G:
  G{[Spec{KCopy{}, SPayA{}}, Spec{KFn{}, SPayB{}}],
    [Link{New{0n, 0n}, New{1n, 0n}}, Link{New{0n, 1n}, Ext{0n}}, Link{New{0n, 2n}, Ext{1n}}, Link{New{1n, 1n}, New{1n, 2n}}]}

# the identity function copied is two identities, each at its level: the
# copy and the merge the rule makes meet, of one fan's identity, and
# annihilate (law copy_identity). In canonical order: external peers 0
# and 1 face the two functions' principals, then each function, its
# source the original's, its body facing its variable.
def copy_identity() -> Bool:
  ex.eq(loop.after.n(fz.after(lf.apply(rule(KCopy{}, KFn{}, True{}), loop.copy.g(), 0n, 1n))),
    [10n, 14n, 0n, 0n, 0n, 1n, 2n, 1n, 12n, 11n, 1n, 2n, 2n, 16n, 15n])
