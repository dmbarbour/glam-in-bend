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

# the rule for A meeting B, A's principal negative. t tests the payloads:
# for two fans, whether they are residuals of one duplication; for an
# application meeting data, whether the data is a builtin function; for
# an application meeting a function, whether their levels agree
def rule(a: NodeKind, b: NodeKind, t: Bool) -> Rule:
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
