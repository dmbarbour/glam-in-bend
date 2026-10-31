import Base
import ../rules.bend as R
import ../net.bend as N
import ../kprim.bend as P

# Writes spike/krules.bend: the kernel's rewrites, generated from the rule
# table (R.rule), so the rules that run are the rules the laws are proved
# over (spike-node-layout in docs/plans/EvalSpike_2026-10-26.md; the
# workaround for compile-time specialization in docs/BendIssues.md).
# scripts/check.sh regenerates the file and fails on any difference.
#
#   bend spike/tools/gen_krules.bend > spike/krules.bend
#
# A rule becomes a chain of functions: the first frees the redex and makes
# the first new node; step j takes node j - 1 and makes node j; the last
# step links, in the table's order. The chain is written last step first,
# a callee preceding its caller. The code assumes no external peer is a
# port of the redex itself; the kernel sends such redexes through its
# interpreter of the table instead.

def kinds() -> List<&2, R.NodeKind>:
  [R.KFree{}, R.KFn{}, R.KAp{}, R.KCopy{}, R.KMerge{}, R.KData{}, R.KEraN{}, R.KEraP{}, R.KRoot{}, R.KCall{}, R.KLift{}, R.KLiftC{}, R.KCopyL{}, R.KCopyR{}, R.KMergeL{}, R.KMergeR{}, R.KDCall{}]

def kname(k: R.NodeKind) -> String:
  match k:
    case R.KFree{}:
      "Free"
    case R.KFn{}:
      "Fn"
    case R.KAp{}:
      "Ap"
    case R.KCopy{}:
      "Copy"
    case R.KMerge{}:
      "Merge"
    case R.KData{}:
      "Data"
    case R.KEraN{}:
      "EraN"
    case R.KEraP{}:
      "EraP"
    case R.KRoot{}:
      "Root"
    case R.KCall{}:
      "Call"
    case R.KLift{}:
      "Lift"
    case R.KLiftC{}:
      "LiftC"
    case R.KCopyL{}:
      "CopyL"
    case R.KCopyR{}:
      "CopyR"
    case R.KMergeL{}:
      "MergeL"
    case R.KMergeR{}:
      "MergeR"
    case R.KDCall{}:
      "DCall"

def code(+k: R.NodeKind) -> String:
  U32.show(N.kcode(k))

# What a kind's payload word holds (heap-strategies.kinds.payloads): a
# value, data or a call's or a dead call's function, its table entry the
# node's to drop; a control's index and offset; or nothing, a fan's
# identity and a level being in the header. Every kind is named, so that
# a new one must be placed.
type Holds is Data:
  HNone{}
  HValue{}
  HCtl{}

def holds(k: R.NodeKind) -> Holds:
  match k:
    case R.KFree{}:
      HNone{}
    case R.KFn{}:
      HNone{}
    case R.KAp{}:
      HNone{}
    case R.KCopy{}:
      HNone{}
    case R.KMerge{}:
      HNone{}
    case R.KData{}:
      HValue{}
    case R.KEraN{}:
      HNone{}
    case R.KEraP{}:
      HNone{}
    case R.KRoot{}:
      HNone{}
    case R.KCall{}:
      HValue{}
    case R.KLift{}:
      HCtl{}
    case R.KLiftC{}:
      HCtl{}
    case R.KCopyL{}:
      HNone{}
    case R.KCopyR{}:
      HNone{}
    case R.KMergeL{}:
      HNone{}
    case R.KMergeR{}:
      HNone{}
    case R.KDCall{}:
      HValue{}

def is_value(h: Holds) -> Bool:
  match h:
    case HValue{}:
      True{}
    case _:
      False{}

def is_some_pay(h: Holds) -> Bool:
  match h:
    case HNone{}:
      False{}
    case _:
      True{}

def is_data(k: R.NodeKind) -> Bool:
  is_value(holds(k))

def has_pay(k: R.NodeKind) -> Bool:
  is_some_pay(holds(k))

# a new node's header and payload word, by source; a payload carries its
# value form with it (SApply's value is made by a step of its own), and a
# fan's or a lifted level the form marking a net built without levels
def hdr(+k: R.NodeKind, s: R.Src) -> String:
  match s:
    case R.SPayA{}:
      "P.hd2(" ++ code(k) ++ ", P.form(ha), P.fld(ha))"
    case R.SPayB{}:
      "P.hd2(" ++ code(k) ++ ", P.form(hb), P.fld(hb))"
    case R.SFanA{}:
      "P.hd2(" ++ code(k) ++ ", P.form(ha), P.fld(ha))"
    case R.SFanB{}:
      "P.hd2(" ++ code(k) ++ ", P.form(hb), P.fld(hb))"
    case R.SLiftA{}:
      "P.hd2(" ++ code(k) ++ ", P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha)))"
    case R.SLiftB{}:
      "P.hd2(" ++ code(k) ++ ", P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb)))"
    case _:
      "P.hd(" ++ code(k) ++ ", 0)"

def pword(s: R.Src) -> String:
  match s:
    case R.SPayA{}:
      "pa"
    case R.SPayB{}:
      "pb"
    case R.SLiftA{}:
      "pa"
    case R.SLiftB{}:
      "pb"
    case _:
      "0"

def is_apply(s: R.Src) -> Bool:
  match s:
    case R.SApply{}:
      True{}
    case _:
      False{}

def spec_kind(sp: R.Spec) -> R.NodeKind:
  match sp:
    case R.Spec{+k, s}:
      k

def spec_at(xs: List<&2, R.Spec>, j: Nat) -> R.Spec:
  match xs j:
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+i:
      spec_at(t, i)
    case Nil{} _:
      R.Spec{R.KFree{}, R.SNone{}}

# a reference to port p of new node j
def new_end(+j: Nat, +p: Nat) -> String:
  match p:
    case 0n:
      "n" ++ Nat.show(j)
    case _:
      "(n" ++ Nat.show(j) ++ " + " ++ Nat.show(p) ++ " : U32)"

def end(+xs: List<&2, R.Spec>, e: R.End) -> String:
  match e:
    case R.Ext{i}:
      "e" ++ Nat.show(i)
    case R.New{+j, +p}:
      new_end(j, p)

def links(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{u, v}, t}:
      links(xs, t, "P.link(" ++ acc ++ ", " ++ end(xs, u) ++ ", " ++ end(xs, v) ++ ")")

def note_if(c: Bool, +acc: String, +u: String, +v: String) -> String:
  match c:
    case True{}:
      "note(" ++ acc ++ ", " ++ u ++ ", " ++ v ++ ")"
    case False{}:
      acc

# the eager family's notes: each link that may join two principal ports
# (R.may_pri, as R.pairs_made counts them), in the order links makes them
def notes(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{+u, +v}, t}:
      notes(xs, t, note_if(R.may_pri(u) && R.may_pri(v), acc, end(xs, u), end(xs, v)))

# One family of rewrites (spike-templates), written once and generic over
# what a strategy threads beside the net (knet.bend's Families): S, a
# strategy's stack or nothing; `note`, a link the rewrite makes between two
# principal ports noted on it, in the table's order; R and `fin`, the
# result made of the net and S. A rule's rewrite (w) takes `after` too,
# what follows it, and returns R; an event's takes S and `note` alone and
# returns the net and S.

def common() -> String:
  "st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32"

def common_args() -> String:
  "st, a, b, ha, hb, pa, pb, e0, e1, e2, e3"

# parameters, and arguments, n0 .. n(j - 1)
def made_params(j: Nat, +i: Nat) -> String:
  match j:
    case 0n:
      ""
    case 1n+p:
      ", +n" ++ Nat.show(i) ++ ": U32" ++ made_params(p, 1n+i)

def made_args(j: Nat, +i: Nat) -> String:
  match j:
    case 0n:
      ""
    case 1n+p:
      ", n" ++ Nat.show(i) ++ made_args(p, 1n+i)

def stepname(+name: String, +j: Nat) -> String:
  name ++ ".k" ++ Nat.show(j)

# Templates
# ---------
#
# A rule's rewrite calls `after`, what follows it (knet.bend's go.none, or
# the events' ev.settle), given the rule's sites: each strategy's copy of
# the rewrite chain then has its own copy of every rewrite beneath, each
# called once, which Bend folds into its caller
# (heap-strategies.erasure.kernel.parity). A rule with no site calls no
# `after`. An event's rewrite (w false) has no `after`: the events' loop
# alone calls it.

def tparam(w: Bool) -> String:
  match w:
    case True{}:
      "~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, "
    case False{}:
      "~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, "

def targ(w: Bool) -> String:
  match w:
    case True{}:
      "~S, ~R, ~note, ~fin, ~after, "
    case False{}:
      "~S, ~note, "

def ret(w: Bool) -> String:
  match w:
    case True{}:
      "R"
    case False{}:
      "P.H & S"

def finish.w(w: Bool, +x: String, +ss: String) -> String:
  match w:
    case True{}:
      "after(" ++ x ++ ", " ++ ss ++ ")"
    case False{}:
      x

# Linear payloads
# ---------------
#
# A data node's or a call's payload may be a table entry with one owner:
# the first new node using it takes it over, each later one gets a
# duplicate, and a rule using it nowhere drops it. SApply takes both.

def uses_a(s: R.Src) -> Nat:
  match s:
    case R.SPayA{}:
      1n
    case _:
      0n

def uses_b(s: R.Src) -> Nat:
  match s:
    case R.SPayB{}:
      1n
    case _:
      0n

def uses_x(+isa: Bool, s: R.Src) -> Nat:
  match isa:
    case True{}:
      uses_a(s)
    case False{}:
      uses_b(s)

# uses of A's (isa) or B's payload among the first j specs
def uses(xs: List<&2, R.Spec>, +isa: Bool, j: Nat) -> Nat:
  match xs j:
    case Con{R.Spec{k, s}, t} 1n+i:
      Nat.add(uses_x(isa, s), uses(t, isa, i))
    case _ _:
      0n

def has_apply(xs: List<&2, R.Spec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{R.Spec{k, s}, t}:
      is_apply(s) || has_apply(t)

# kinds of step before making a node: none, computing, duplicating
type Pre is Data:
  PNo{}
  PAp{}
  PDup{+isa: Bool}

def pre_x(+dup: Bool, +isa: Bool) -> Pre:
  match dup:
    case True{}:
      PDup{isa}
    case False{}:
      PNo{}

def pre_of(sp: R.Spec, +xs: List<&2, R.Spec>, +j: Nat, +a: R.NodeKind, +b: R.NodeKind) -> Pre:
  match sp:
    case R.Spec{k, s}:
      match s:
        case R.SApply{}:
          PAp{}
        case R.SPayA{}:
          pre_x(is_data(a) && Nat.is_gt(uses(xs, True{}, j), 0n), True{})
        case R.SPayB{}:
          pre_x(is_data(b) && Nat.is_gt(uses(xs, False{}, j), 0n), False{})
        case _:
          PNo{}

def side(+isa: Bool) -> String:
  match isa:
    case True{}:
      "a"
    case False{}:
      "b"

# Nodes in place (heap-strategies.reuse): a rule's first two new nodes take
# the redex's two slots, a's then b's, as the free list would have handed
# them back, so the net is the same node for node with no free list
# traffic; a rule making one frees b alone, one making none both.

def slot.go(first: Bool, +j: Nat) -> String:
  match first:
    case True{}:
      "a"
    case False{}:
      "b"

# node j's call: in slot a or b, or from the free list after those
def node_call.go(reuse: Bool, +j: Nat, +st: String) -> String:
  match reuse:
    case True{}:
      "P.renode(" ++ st ++ ", " ++ slot.go(Nat.is_eq(j, 0n), j) ++ ", "
    case False{}:
      "P.node(" ++ st ++ ", "

def node_call(+j: Nat, +st: String) -> String:
  node_call.go(Nat.is_lt(j, 2n), j, st)

def node_pw_call.go(reuse: Bool, +j: Nat) -> String:
  match reuse:
    case True{}:
      "P.renode_pw(h, " ++ slot.go(Nat.is_eq(j, 0n), j) ++ ", "
    case False{}:
      "P.node_pw(h, "

def node_pw_call(+j: Nat) -> String:
  node_pw_call.go(Nat.is_lt(j, 2n), j)

# making node j (spec sp, step kind pre) on state `st`, then step j + 1
def make_call(+w: Bool, +name: String, +st: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_call(j, st) ++ hdr(k, s) ++ ", " ++ pword(s) ++ "), " ++ common_args() ++ made_args(j, 0n) ++ ")"
        case PAp{}:
          stepname(name, 1n+j) ++ ".pre(" ++ targ(w) ++ "P.apply(" ++ st ++ ", ha, pa, hb, pb), " ++ common_args() ++ made_args(j, 0n) ++ ")"
        case PDup{+isa}:
          stepname(name, 1n+j) ++ ".pre(" ++ targ(w) ++ "P.dup(" ++ st ++ ", P.form(h" ++ side(isa) ++ "), p" ++ side(isa) ++ "), " ++ common_args() ++ made_args(j, 0n) ++ ")"

# the step taking a computed value or a duplicate, making node j
def pre_fn(+w: Bool, +name: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          ""
        case PAp{}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(" ++ tparam(w) ++ "r: P.H & P.PW, " ++ common() ++ made_params(j, 0n) ++ ") -> " ++ ret(w) ++ ":\n" ++
            "  (h, pw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_pw_call(j) ++ code(k) ++ ", pw), " ++ common_args() ++ made_args(j, 0n) ++ ")\n\n"
        case PDup{+isa}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(" ++ tparam(w) ++ "r: P.H & U32, " ++ common() ++ made_params(j, 0n) ++ ") -> " ++ ret(w) ++ ":\n" ++
            "  (h, +dw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_call(j, "h") ++ hdr(k, s) ++ ", dw), " ++ common_args() ++ made_args(j, 0n) ++ ")\n\n"

# Sites
# -----
#
# Where a rule's rewrite may make an event, the external peers looked at
# after it (heap-strategies.erasure.kernel.sites): one facing a new
# eraser's principal; one facing a new node's auxiliary port at which an
# eraser makes an event; one end of each wire joining two external peers,
# the other end read through it. A peer facing a new node's principal is
# an active pair if anything, and the links between new nodes make no
# event (inner_events). The rest are passed as none.

def is_stuck(r: R.Rule) -> Bool:
  match r:
    case R.RStuck{}:
      True{}
    case _:
      False{}

def eraser_codes() -> List<&2, R.NodeKind>:
  [R.KEraN{}, R.KEraP{}]

def is_eraser(k: R.NodeKind) -> Bool:
  match k:
    case R.KEraN{}:
      True{}
    case R.KEraP{}:
      True{}
    case _:
      False{}

def ev_eraser.hit(stuck: Bool, +b: R.NodeKind, rest: Maybe<&2, R.NodeKind>) -> Maybe<&2, R.NodeKind>:
  match stuck:
    case True{}:
      rest
    case False{}:
      Some{b}

# the eraser making an event at port p of kind a, if any
def ev_eraser(es: List<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat) -> Maybe<&2, R.NodeKind>:
  match es:
    case Nil{}:
      None{}
    case Con{+b, t}:
      ev_eraser.hit(is_stuck(R.event(a, b, p)), b, ev_eraser(t, a, p))

def ev_port(+k: R.NodeKind, +p: Nat) -> Bool:
  Maybe.is_some(&2, R.NodeKind, ev_eraser(eraser_codes(), k, p))

def site.end(+xs: List<&2, R.Spec>, e: R.End, +i: Nat) -> Bool:
  match e:
    case R.New{+j, +p}:
      match p:
        case 0n:
          is_eraser(spec_kind(spec_at(xs, j)))
        case _:
          ev_port(spec_kind(spec_at(xs, j)), p)
    case R.Ext{+k}:
      Nat.is_gt(k, i)

def is_ext(e: R.End, +i: Nat) -> Bool:
  match e:
    case R.Ext{+k}:
      Nat.is_eq(k, i)
    case R.New{j, p}:
      False{}

# may external peer i be in an event after the rule's links?
def site(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +i: Nat) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{R.Link{+u, +v}, t}:
      (is_ext(u, i) && site.end(xs, v, i)) || (is_ext(v, i) && site.end(xs, u, i)) || site(xs, t, i)

def site.s(b: Bool, +i: Nat) -> String:
  match b:
    case True{}:
      "e" ++ Nat.show(i)
    case False{}:
      "P.nil()"

def any_site(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> Bool:
  site(xs, ls, 0n) || site(xs, ls, 1n) || site(xs, ls, 2n) || site(xs, ls, 3n)

def sites(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> String:
  "N.Ext4{" ++ site.s(site(xs, ls, 0n), 0n) ++ ", " ++ site.s(site(xs, ls, 1n), 1n) ++ ", " ++
    site.s(site(xs, ls, 2n), 2n) ++ ", " ++ site.s(site(xs, ls, 3n), 3n) ++ "}"

# Fusing controls
# ---------------
#
# After its links, a rewrite tries fusion on each link it made that may
# join two controls of one kind (net.bend's fuse_ends), in the table's
# order.

def fuses(+xs: List<&2, R.Spec>, es: List<&2, R.End>, +acc: String) -> String:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      fuses(xs, t, "P.fuse(" ++ acc ++ ", " ++ end(xs, e) ++ ")")

# the links, then the fusion attempts
def finish.e(w: Bool, +hs: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> String:
  match w:
    case True{}:
      "fin(" ++ hs ++ ", " ++ notes(xs, ls, "st") ++ ")"
    case False{}:
      "(" ++ hs ++ ", " ++ notes(xs, ls, "st") ++ ")"

def finish(+w: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +st: String) -> String:
  finish.w(w && any_site(xs, ls), finish.e(w, fuses(xs, N.fuse_ends(xs, ls), links(xs, ls, st)), xs, ls), sites(xs, ls))

def step_body(+w: Bool, last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      finish(w, xs, ls, "h")
    case False{}:
      make_call(w, name, "h", j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

def step_pre(+w: Bool, last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      ""
    case False{}:
      pre_fn(w, name, j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

# step j (1 .. n), taking node j - 1
def step_fn(+w: Bool, +name: String, +j: Nat, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  step_pre(w, Nat.is_ge(j, n), name, j, xs, a, b) ++
  "def " ++ stepname(name, j) ++ "(" ++ tparam(w) ++ "r: P.H & U32, " ++ common() ++ made_params(Nat.sub(j, 1n), 0n) ++ ") -> " ++ ret(w) ++ ":\n" ++
    "  (h, +n" ++ Nat.show(Nat.sub(j, 1n)) ++ ") = r\n" ++
    "  " ++ step_body(w, Nat.is_ge(j, n), name, j, xs, ls, a, b) ++ "\n\n"

# steps m down to 1
def steps(+w: Bool, +m: Nat, +name: String, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match m:
    case 0n:
      ""
    case 1n+p:
      step_fn(w, name, m, n, xs, ls, a, b) ++ steps(w, p, name, n, xs, ls, a, b)

def drop_if(d: Bool, +st: String, +isa: Bool) -> String:
  match d:
    case True{}:
      "P.drop(" ++ st ++ ", P.form(h" ++ side(isa) ++ "), p" ++ side(isa) ++ ")"
    case False{}:
      st

def free.one(one: Bool) -> String:
  match one:
    case True{}:
      "P.free(h, b)"
    case False{}:
      "h"

# the redex's slots no new node takes, freed: both for a rule making
# none, b's for one making one
def free_of(+n: Nat) -> String:
  match n:
    case 0n:
      "P.fresh2(h, a, b)"
    case 1n+p:
      free.one(Nat.is_eq(p, 0n))

# the state after freeing the redex: a data payload no new node uses,
# dropped
def start(+xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  drop_if(is_data(b) && Nat.is_eq(uses(xs, False{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
    drop_if(is_data(a) && Nat.is_eq(uses(xs, True{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
      free_of(List.length(&2, R.Spec, xs)), True{}), False{})

def entry(+w: Bool, +name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match xs:
    case Nil{}:
      "def " ++ name ++ "(" ++ tparam(w) ++ "h: P.H, " ++ common() ++ ") -> " ++ ret(w) ++ ":\n" ++
        "  " ++ finish(w, xs, ls, start(xs, a, b)) ++ "\n\n"
    case Con{sp, t}:
      steps(w, List.length(&2, R.Spec, xs), name, List.length(&2, R.Spec, xs), xs, ls, a, b) ++
        pre_fn(w, name, 0n, sp, pre_of(sp, xs, 0n, a, b)) ++
        "def " ++ name ++ "(" ++ tparam(w) ++ "h: P.H, " ++ common() ++ ") -> " ++ ret(w) ++ ":\n" ++
        "  " ++ make_call(w, name, start(xs, a, b), 0n, sp, pre_of(sp, xs, 0n, a, b)) ++ "\n\n"

# a rule's functions, the first named `name`
def rule_fns(+w: Bool, r: R.Rule, +name: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match r:
    case R.RStuck{}:
      ""
    case R.RWire{+xs, +ls}:
      entry(w, name, xs, ls, a, b)

# Level checks
# ------------
#
# Assertions counted as errors, the rewrite proceeding (net.bend's
# violation): a copy meeting a function at a level not below its own, and
# a control raising a level, or another control's index, past the field's
# range. Kinds without a level (data, erasers, the root, calls) cannot be
# raised past it. The spike's check of two fans' sites at one level needs
# the site, which a leveled fan here does not keep.

def lift_a() -> String:
  "P.lift_wraps(P.fld(ha), pa, P.fld(hb))"

def lift_b() -> String:
  "P.lift_wraps(P.fld(hb), pb, P.fld(ha))"

def check_expr.full(+a: R.NodeKind, +b: R.NodeKind) -> String:
  match a b:
    case R.KCopy{} R.KFn{}:
      "P.copy_fn_bad(ha, hb)"
    case R.KLift{} R.KFn{}:
      lift_a()
    case R.KLift{} R.KMerge{}:
      lift_a()
    case R.KLift{} R.KLiftC{}:
      lift_a() ++ " || " ++ lift_b()
    case R.KAp{} R.KLiftC{}:
      lift_b()
    case R.KCopy{} R.KLiftC{}:
      lift_b()
    case _ _:
      ""

# a linear fan's pairs are checked as its full fan's
def check_expr(+a: R.NodeKind, +b: R.NodeKind) -> String:
  check_expr.full(R.lf.full(a), R.lf.full(b))

# the state a pair's rewrite starts from: h, checked
def checked.e(none: Bool, +e: String) -> String:
  match none:
    case True{}:
      "h"
    case False{}:
      "P.err_if(" ++ e ++ ", h)"

def checked(+a: R.NodeKind, +b: R.NodeKind) -> String:
  checked.e(String.eq(check_expr(a, b), ""), check_expr(a, b))

# a stuck pair's state: the net as it is, its errors counted
def call.s(st: Bool, +name: String, +hs: String) -> String:
  match st:
    case True{}:
      "fin(P.err_if(U32.is_ne(ka, 8), " ++ hs ++ "), st)"
    case False{}:
      name ++ "(" ++ targ(True{}) ++ hs ++ ", " ++ common_args() ++ ")"

def call(r: R.Rule, +name: String, +hs: String) -> String:
  call.s(is_stuck(r), name, hs)

# Pairs
# =====

def pname(+a: R.NodeKind, +b: R.NodeKind) -> String:
  "rw." ++ kname(a) ++ "." ++ kname(b)

# do the rule's two variants, for t true and false, differ?
def differs(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  Bool.not(String.eq(rule_fns(True{}, R.rule(a, b, True{}), "x", a, b), rule_fns(True{}, R.rule(a, b, False{}), "x", a, b)))

def both_stuck(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  is_stuck(R.rule(a, b, True{})) && is_stuck(R.rule(a, b, False{}))

# Peeling: a Lift and a LiftC meeting at one index as different runs of
# units are peeled first (kprim.bend's peel_ctl, fuse-control-runs),
# which gives the payload test on what is left and the new peers of their
# ports 1; only this pair pays for it
def is_ctl_pair(a: R.NodeKind, b: R.NodeKind) -> Bool:
  match a b:
    case R.KLift{} R.KLiftC{}:
      True{}
    case _ _:
      False{}

def peeled_fn(+a: R.NodeKind, +b: R.NodeKind) -> String:
  "def " ++ pname(a, b) ++ ".peeled(" ++ tparam(True{}) ++ "r: P.Pl, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> R:\n" ++
  "  match r:\n" ++
  "    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:\n" ++
  "      match t:\n" ++
  "        case True{}:\n" ++
  "          " ++ pname(a, b) ++ ".yes(" ++ targ(True{}) ++ "h, " ++ common_args() ++ ")\n" ++
  "        case False{}:\n" ++
  "          " ++ pname(a, b) ++ ".no(" ++ targ(True{}) ++ "h, " ++ common_args() ++ ")\n\n"

def peeled_fns(c: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      peeled_fn(a, b)
    case False{}:
      ""

def pair_fns.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      rule_fns(True{}, R.rule(a, b, True{}), pname(a, b) ++ ".yes", a, b) ++ rule_fns(True{}, R.rule(a, b, False{}), pname(a, b) ++ ".no", a, b) ++
        peeled_fns(is_ctl_pair(a, b), a, b)
    case False{}:
      rule_fns(True{}, R.rule(a, b, False{}), pname(a, b), a, b)

def pair_fns(+a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_fns.d(differs(a, b), a, b)

def pair_case.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      match t:\n" ++
      "        case True{}:\n" ++
      "          " ++ call(R.rule(a, b, True{}), pname(a, b) ++ ".yes", checked(a, b)) ++ "\n" ++
      "        case False{}:\n" ++
      "          " ++ call(R.rule(a, b, False{}), pname(a, b) ++ ".no", checked(a, b)) ++ "\n"
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      " ++ call(R.rule(a, b, False{}), pname(a, b), checked(a, b)) ++ "\n"

def pair_case.p(c: Bool, +d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      " ++ pname(a, b) ++ ".peeled(" ++ targ(True{}) ++ "P.peel_ctl(" ++ checked(a, b) ++ ", a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)\n"
    case False{}:
      pair_case.d(d, a, b)

def pair_case.s(s: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match s:
    case True{}:
      ""
    case False{}:
      pair_case.p(is_ctl_pair(a, b), differs(a, b), a, b)

def pair_case(+a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_case.s(both_stuck(a, b), a, b)

def pick(b: Bool, +x: String, +y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def over_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind, +fns: Bool) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      pick(fns, pair_fns(a, b), pair_case(a, b)) ++ over_b(t, a, fns)

def check_case.e(none: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match none:
    case True{}:
      ""
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n      " ++ checked(a, b) ++ "\n"

def check_case(+a: R.NodeKind, +b: R.NodeKind) -> String:
  check_case.e(String.eq(check_expr(a, b), ""), a, b)

def checks_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      check_case(a, b) ++ checks_b(t, a)

def checks_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      checks_b(kinds(), a) ++ checks_a(t)

# Payload tests: where a rule's two variants differ (R.rule's t), the test
# on the payloads that picks one (net.bend's rule_test). A Lift facing a
# LiftC is tested after peeling instead (P.peel_ctl).
def test_expr.full(+a: R.NodeKind, +b: R.NodeKind) -> String:
  match a b:
    case R.KAp{} R.KFn{}:
      "(h, P.same_lvl(ha, hb))"
    case R.KAp{} R.KData{}:
      "P.val_is_fn(h, P.form(hb), P.fld(hb), pb)"
    case R.KCopy{} R.KMerge{}:
      "(h, P.same_lvl(ha, hb))"
    case _ _:
      ""

# a linear fan's pairs are tested as its full fan's
def test_expr(+a: R.NodeKind, +b: R.NodeKind) -> String:
  test_expr.full(R.lf.full(a), R.lf.full(b))

# a pair whose variants differ and which has no test here names itself in
# code that does not compile
def test_or_missing(none: Bool, +x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match none:
    case True{}:
      "missing_payload_test_" ++ kname(a) ++ "_" ++ kname(b)
    case False{}:
      x

def test_case.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n      " ++ test_or_missing(String.eq(test_expr(a, b), ""), test_expr(a, b), a, b) ++ "\n"
    case False{}:
      ""

def test_case(+a: R.NodeKind, +b: R.NodeKind) -> String:
  test_case.d(differs(a, b) && Bool.not(is_ctl_pair(a, b)), a, b)

def tests_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      test_case(a, b) ++ tests_b(t, a)

def tests_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      tests_b(kinds(), a) ++ tests_a(t)

# the payload test, a template over the family and what follows, for a
# copy in each strategy's chain
def tests() -> String:
  "def test.k(" ++ tparam(True{}) ++ "+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  match ka kb:\n" ++ tests_a(kinds()) ++ "    case _ _:\n      (h, False{})\n\n" ++
  "def test(" ++ tparam(True{}) ++ "h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  test.k(" ++ targ(True{}) ++ "P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)\n\n"

# Growth: does a rule make more nodes than the two it frees? The pairs a
# two-stack strategy defers (heap-strategies.twostack). Where the two
# variants differ, the payload test on the headers alone decides, true
# for the variant that does not grow.
def grows_r(r: R.Rule) -> Bool:
  match r:
    case R.RWire{xs, ls}:
      Nat.is_lt(2n, List.length(&2, R.Spec, xs))
    case R.RStuck{}:
      False{}

def grow_test.full(+a: R.NodeKind, +b: R.NodeKind) -> String:
  match a b:
    case R.KCopy{} R.KMerge{}:
      "P.same_lvl(ha, hb)"
    case _ _:
      ""

# a linear fan's pairs are tested as its full fan's
def grow_test(+a: R.NodeKind, +b: R.NodeKind) -> String:
  grow_test.full(R.lf.full(a), R.lf.full(b))

def grow_tested(none: Bool, +x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match none:
    case True{}:
      "missing_growth_test_" ++ kname(a) ++ "_" ++ kname(b)
    case False{}:
      x

def grow_expr(+gy: Bool, +gn: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match gy gn:
    case True{} True{}:
      "True{}"
    case False{} False{}:
      ""
    case False{} True{}:
      "Bool.not(" ++ grow_tested(String.eq(grow_test(a, b), ""), grow_test(a, b), a, b) ++ ")"
    case True{} False{}:
      grow_tested(String.eq(grow_test(a, b), ""), grow_test(a, b), a, b)

def grow_case.e(none: Bool, +x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match none:
    case True{}:
      ""
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n      " ++ x ++ "\n"

def grow_case(+a: R.NodeKind, +b: R.NodeKind) -> String:
  grow_case.e(String.eq(grow_expr(grows_r(R.rule(a, b, True{})), grows_r(R.rule(a, b, False{})), a, b), ""),
    grow_expr(grows_r(R.rule(a, b, True{})), grows_r(R.rule(a, b, False{})), a, b), a, b)

def grows_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      grow_case(a, b) ++ grows_b(t, a)

def grows_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      grows_b(kinds(), a) ++ grows_a(t)

def max.go(lt: Bool, +a: Nat, +b: Nat) -> Nat:
  match lt:
    case True{}:
      b
    case False{}:
      a

def nat_max(+a: Nat, +b: Nat) -> Nat:
  max.go(Nat.is_lt(a, b), a, b)

def most_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind, +m: Nat) -> Nat:
  match bs:
    case Nil{}:
      m
    case Con{+b, t}:
      most_b(t, a, nat_max(m, nat_max(R.pairs_made(R.rule(a, b, True{})), R.pairs_made(R.rule(a, b, False{})))))

# the most active pairs any rewrite in the table makes
def most_a(as: List<&2, R.NodeKind>, +m: Nat) -> Nat:
  match as:
    case Nil{}:
      m
    case Con{+a, t}:
      most_a(t, most_b(kinds(), a, m))

def over_a(as: List<&2, R.NodeKind>, +fns: Bool) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      over_b(kinds(), a, fns) ++ over_a(t, fns)

def neg_str.b(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def neg_str(+k: R.NodeKind) -> String:
  neg_str.b(R.pol_eq(R.port_pol(k, 0n), R.Neg{}))

def tables.k(ks: List<&2, R.NodeKind>, +neg: Bool) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      "    case " ++ code(k) ++ ":\n      " ++ pick(neg, neg_str(k), U32.show(U32.from_nat(R.arity(k)))) ++ "\n" ++ tables.k(t, neg)

# ports and principal polarity by kind code (R.arity, R.port_pol)
def tables() -> String:
  "# ports by kind code (R.arity)\n" ++
  "def kind_arity(+k: U32) -> U32:\n  match k:\n" ++ tables.k(kinds(), False{}) ++ "    case _:\n      0\n\n" ++
  "# 1 where the principal port is negative (R.port_pol): a table, where a\n" ++
  "# match whose arms are constructors would be a chain\n" ++
  "def kind_neg.n(+k: U32) -> U32:\n  match k:\n" ++ tables.k(kinds(), True{}) ++ "    case _:\n      0\n\n" ++
  "def kind_neg(+k: U32) -> Bool:\n  U32.is_eq(kind_neg.n(k), 1)\n\n"

def payloads.d(ks: List<&2, R.NodeKind>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      pick(is_data(k), "    case " ++ code(k) ++ ":\n      True{}\n", "") ++ payloads.d(t)

# the word, of a node's 2 and 3, kprim.bend's node.word puts a payload in
def payload.w(+k: R.NodeKind) -> String:
  pick(U32.is_eq(P.node.word.k(N.kcode(k)), 2), "w2", "w3")

def payloads.w(ks: List<&2, R.NodeKind>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      pick(has_pay(k), "    case " ++ code(k) ++ ":\n      " ++ payload.w(k) ++ "\n", "") ++ payloads.w(t)

# which kinds hold a value, and where each kind with a payload word holds
# it, for the kernel's rewrites, interpreter, audit and sweep
def payloads() -> String:
  "# a kind whose payload is a value, data or a call's or a dead call's\n" ++
  "# function: a table entry the node's to drop\n" ++
  "def is_data(+k: U32) -> Bool:\n  match k:\n" ++ payloads.d(kinds()) ++ "    case _:\n      False{}\n\n" ++
  "# a node's payload, of w2 and w3, its words 2 and 3, where kprim.bend's\n" ++
  "# node.word puts it: a value or a control's index and offset; 0 for none\n" ++
  "def payload.k(+k: U32, +w2: U32, +w3: U32) -> U32:\n  match k:\n" ++ payloads.w(kinds()) ++ "    case _:\n      0\n\n"

def stuck_v(+t: Bool, +f: Bool) -> String:
  match t f:
    case True{} True{}:
      "1"
    case False{} False{}:
      "0"
    case True{} False{}:
      "3"
    case False{} True{}:
      "2"

def stuck_case.s(s: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match s:
    case True{}:
      ""
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n      " ++
        stuck_v(is_stuck(R.rule(a, b, True{})), is_stuck(R.rule(a, b, False{}))) ++ "\n"

def stuck_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      stuck_case.s(both_stuck(a, b), a, b) ++ stuck_b(t, a)

def stuck_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      stuck_b(kinds(), a) ++ stuck_a(t)

# Events
# ------
#
# heap-strategies.erasure.kernel: an eraser's principal facing an
# auxiliary port (R.event, A the node and B the eraser). The kernel looks
# for events at a rewrite's external peers (knet.bend's Events), so a rule
# linking two of its own new nodes into an event would go unseen; the
# file fails to compile if one does (inner_events). An event's rewrite is
# a rule's, its new node 0 in A's slot, its external peer 0 the peer of A's
# principal: their link is A's own, left as it is, so neither made nor
# noted again, while A's pair, if A is in one, keeps its place on the
# stack.

def is_n00(e: R.End) -> Bool:
  match e:
    case R.New{+j, +p}:
      Nat.is_eq(j, 0n) && Nat.is_eq(p, 0n)
    case R.Ext{i}:
      False{}

def is_x0(e: R.End) -> Bool:
  match e:
    case R.Ext{+i}:
      Nat.is_eq(i, 0n)
    case R.New{j, p}:
      False{}

def ev_kept(+u: R.End, +v: R.End) -> Bool:
  Bool.not((is_n00(u) && is_x0(v)) || (is_x0(u) && is_n00(v)))

def ev_links.go(keep: Bool, l: R.Link, t: List<&2, R.Link>) -> List<&2, R.Link>:
  match keep:
    case True{}:
      Con{l, t}
    case False{}:
      t

# an event's links but the one A's principal keeps
def ev_links(ls: List<&2, R.Link>) -> List<&2, R.Link>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{R.Link{+u, +v}, t}:
      ev_links.go(ev_kept(u, v), R.Link{u, v}, ev_links(t))

def ev_rule(r: R.Rule) -> R.Rule:
  match r:
    case R.RWire{xs, ls}:
      R.RWire{xs, ev_links(ls)}
    case R.RStuck{}:
      R.RStuck{}

def ev_name(+a: R.NodeKind, +p: Nat) -> String:
  "ev." ++ kname(a) ++ ".p" ++ Nat.show(p)

def ev_ports() -> List<&2, Nat>:
  [1n, 2n]

def first_kind(xs: List<&2, R.Spec>) -> R.NodeKind:
  match xs:
    case Nil{}:
      R.KFree{}
    case Con{R.Spec{+k, s}, t}:
      k

def ev_case(+a: R.NodeKind, +p: Nat, +body: String) -> String:
  "    case " ++ code(a) ++ " " ++ Nat.show(p) ++ ":\n      " ++ body ++ "\n"

def ev_one.f(+f: U32, r: R.Rule, +a: R.NodeKind, +b: R.NodeKind, +p: Nat) -> String:
  match f:
    case 0:
      rule_fns(False{}, ev_rule(r), ev_name(a, p), a, b)
    case _:
      ev_case(a, p, ev_name(a, p) ++ "(" ++ targ(False{}) ++ "h, " ++ common_args() ++ ")")

# over kinds and ports with an event: f 0 the rewrites, 1 the dispatch's
# cases
def ev_one(+f: U32, m: Maybe<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat) -> String:
  match m:
    case None{}:
      ""
    case Some{+b}:
      ev_one.f(f, R.event(a, b, p), a, b, p)

def ev_over_p(+f: U32, ps: List<&2, Nat>, +a: R.NodeKind) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, t}:
      ev_one(f, ev_eraser(eraser_codes(), a, p), a, p) ++ ev_over_p(f, t, a)

def ev_over(+f: U32, as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      ev_over_p(f, ev_ports(), a) ++ ev_over(f, t)

# ev_by's words: two bits a port (0 none, 1 EraN, 2 EraP), eight a kind,
# four kinds a word, so that the check after each rewrite reads a word
# where a match on the kind would make a chain of comparisons (2% to 5% of
# the erasure modes' instructions, measured on a prototype)
def ev_bits.b(b: R.NodeKind) -> U32:
  match b:
    case R.KEraN{}:
      1
    case _:
      2

def ev_bits(m: Maybe<&2, R.NodeKind>, +k: R.NodeKind, +p: Nat) -> U32:
  match m:
    case None{}:
      0
    case Some{+b}:
      (ev_bits.b(b) << U32.to_nat((((N.kcode(k) .&. 3 : U32) * 8 : U32) + (U32.from_nat(p) * 2 : U32) : U32)) : U32)

def ev_word_ps(ps: List<&2, Nat>, +k: R.NodeKind, +acc: U32) -> U32:
  match ps:
    case Nil{}:
      acc
    case Con{+p, t}:
      ev_word_ps(t, k, (acc .|. ev_bits(ev_eraser(eraser_codes(), k, p), k, p) : U32))

def ev_word_k.hit(hit: Bool, +k: R.NodeKind, +acc: U32) -> U32:
  match hit:
    case True{}:
      ev_word_ps(ev_ports(), k, acc)
    case False{}:
      acc

# word w: kinds 4w to 4w + 3
def ev_word_k(ks: List<&2, R.NodeKind>, +w: U32, +acc: U32) -> U32:
  match ks:
    case Nil{}:
      acc
    case Con{+k, t}:
      ev_word_k(t, w, ev_word_k.hit(U32.is_eq((N.kcode(k) >> 2n : U32), w), k, acc))

def ev_most_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat, +m: Nat) -> Nat:
  match bs:
    case Nil{}:
      m
    case Con{+b, t}:
      ev_most_b(t, a, p, nat_max(m, R.pairs_made(ev_rule(R.event(a, b, p)))))

def ev_most_p(ps: List<&2, Nat>, +a: R.NodeKind, +m: Nat) -> Nat:
  match ps:
    case Nil{}:
      m
    case Con{+p, t}:
      ev_most_p(t, a, ev_most_b(eraser_codes(), a, p, m))

# the most active pairs one event makes
def ev_most(as: List<&2, R.NodeKind>, +m: Nat) -> Nat:
  match as:
    case Nil{}:
      m
    case Con{+a, t}:
      ev_most(t, ev_most_p(ev_ports(), a, m))

def spec_k(xs: List<&2, R.Spec>, +j: Nat) -> R.NodeKind:
  spec_kind(spec_at(xs, j))

# an eraser's principal, new node j port p, facing an auxiliary port of
# new node k, port q, that it erases
def inner_ev.dir(+xs: List<&2, R.Spec>, +j: Nat, +p: Nat, +k: Nat, +q: Nat) -> Bool:
  is_eraser(spec_k(xs, j)) && Nat.is_eq(p, 0n) && Nat.is_ne(q, 0n) && Bool.not(is_stuck(R.event(spec_k(xs, k), spec_k(xs, j), q)))

def inner_ev.link(+xs: List<&2, R.Spec>, u: R.End, v: R.End) -> Bool:
  match u v:
    case R.New{+j, +p} R.New{+k, +q}:
      inner_ev.dir(xs, j, p, k, q) || inner_ev.dir(xs, k, q, j, p)
    case _ _:
      False{}

def inner_ev.ls(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{R.Link{u, v}, t}:
      inner_ev.link(xs, u, v) || inner_ev.ls(xs, t)

def inner_ev.r(r: R.Rule) -> Bool:
  match r:
    case R.RWire{+xs, ls}:
      inner_ev.ls(xs, ls)
    case R.RStuck{}:
      False{}

def inner_ev.hit(bad: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match bad:
    case True{}:
      " + inner_event_" ++ kname(a) ++ "_" ++ kname(b)
    case False{}:
      ""

def inner_ev_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      inner_ev.hit(inner_ev.r(R.rule(a, b, True{})) || inner_ev.r(R.rule(a, b, False{})), a, b) ++ inner_ev_b(t, a)

def inner_ev_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      inner_ev_b(kinds(), a) ++ inner_ev_a(t)

def events() -> String:
  "# Events (R.event)\n\n" ++
  "# rules linking two of their own new nodes into an event: none, or this\n" ++
  "# names what does not exist\n" ++
  "def inner_events() -> U32:\n  0" ++ inner_ev_a(kinds()) ++ "\n\n" ++
  "# the eraser kind making an event at port p of kind k, 0 for none: two\n" ++
  "# bits a port (0 none, 1 EraN, 2 EraP), eight a kind, four kinds a word\n" ++
  "def ev_word(+w: U32) -> U32:\n  match w:\n" ++
  "    case 0:\n      " ++ U32.show(ev_word_k(kinds(), 0, 0)) ++ "\n" ++
  "    case 1:\n      " ++ U32.show(ev_word_k(kinds(), 1, 0)) ++ "\n" ++
  "    case 2:\n      " ++ U32.show(ev_word_k(kinds(), 2, 0)) ++ "\n" ++
  "    case _:\n      " ++ U32.show(ev_word_k(kinds(), 3, 0)) ++ "\n\n" ++
  "def ev_by.c(+c: U32) -> U32:\n  match c:\n    case 0:\n      0\n    case _:\n      (c + 5 : U32)\n\n" ++
  "def ev_by(+k: U32, +p: U32) -> U32:\n" ++
  "  ev_by.c(((ev_word((k >> 2n : U32)) >> U32.to_nat((((k .&. 3 : U32) * 8 : U32) + (p * 2 : U32) : U32)) : U32) .&. 3 : U32))\n\n" ++
  "# may port p of kind k be one end of an event: an eraser's principal, or\n" ++
  "# an auxiliary port some eraser makes an event at\n" ++
  "def ev_end(+k: U32, +p: U32) -> Bool:\n" ++
  "  (U32.is_eq(p, 0) && U32.is_eq((k .|. 1 : U32), 7)) || U32.is_ne(ev_by(k, p), 0)\n\n" ++

  "# the most active pairs one event makes\n" ++
  "def ev_most() -> U32:\n  " ++ Nat.show(ev_most(kinds(), 0n)) ++ "\n\n" ++
  ev_over(0, kinds()) ++
  "# the event at port p of a node of kind ka, A, the eraser facing it B;\n" ++
  "# e0 the peer of A's principal, e1 of its other auxiliary port; the net\n" ++
  "# and the family's state, the pairs it makes noted\n" ++
  "def event(" ++ tparam(False{}) ++ "+ka: U32, +p: U32, h: P.H, " ++ common() ++ ") -> P.H & S:\n" ++
  "  match ka p:\n" ++ ev_over(1, kinds()) ++ "    case _ _:\n      (P.h_err(h), st)\n\n"

# Dispatch
# --------
#
# heap-strategies.kinds.dispatch: Bend makes a match on numbers whose arms
# are code a chain of tests of their bits, and one whose arms are
# constants a lookup table (docs/BendIssues.md, "Dispatch on numbers").
# So a pair's rule is numbered by a lookup table on its kinds (rule_no),
# and the number dispatched: the hottest rules tested first, by the
# profiling strategy's pair counts on the standard workloads and the
# random terms (a call meeting a merge, data or a co-control; a control
# meeting a co-control), then a balanced tree of comparisons over the
# rest, 0 for a pair no rule rewrites. Each rule's arm is a function of
# its own, called once. The payload test reads the number too.

type Pr is Data:
  Pr{a: R.NodeKind, b: R.NodeKind}

def hot() -> List<&2, Pr>:
  [Pr{R.KCall{}, R.KMerge{}}, Pr{R.KCall{}, R.KData{}}, Pr{R.KCall{}, R.KLiftC{}}, Pr{R.KLift{}, R.KLiftC{}}]

def pr_eq(+x: Pr, +y: Pr) -> Bool:
  match x y:
    case Pr{+a, +b} Pr{+c, +d}:
      Nat.is_eq(R.kind_n(a), R.kind_n(c)) && Nat.is_eq(R.kind_n(b), R.kind_n(d))

def is_hot(hs: List<&2, Pr>, +p: Pr) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      pr_eq(h, p) || is_hot(t, p)

def keep_pr(c: Bool, +p: Pr, rest: List<&2, Pr>) -> List<&2, Pr>:
  match c:
    case True{}:
      Con{p, rest}
    case False{}:
      rest

def cold_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind) -> List<&2, Pr>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      keep_pr(Bool.not(both_stuck(a, b)) && Bool.not(is_hot(hot(), Pr{a, b})), Pr{a, b}, cold_b(t, a))

def cold_a(as: List<&2, R.NodeKind>) -> List<&2, Pr>:
  match as:
    case Nil{}:
      Nil{}
    case Con{+a, t}:
      List.append(&2, Pr, cold_b(kinds(), a), cold_a(t))

# the rules by number from 1: the rest in the kinds' order, then the hot
def numbered() -> List<&2, Pr>:
  List.append(&2, Pr, cold_a(kinds()), hot())

def n_cold() -> Nat:
  List.length(&2, Pr, cold_a(kinds()))

def n_rules() -> Nat:
  List.length(&2, Pr, numbered())

# the base kinds, each its own class; every code from here up one class,
# the operators' (header-kind-byte)
def n_base() -> Nat:
  List.length(&2, R.NodeKind, kinds())

def pr_ix(+a: R.NodeKind, +b: R.NodeKind) -> Nat:
  Nat.add(Nat.mul(R.kind_n(a), Nat.add(n_base(), 1n)), R.kind_n(b))

def no_at.go(hit: Bool, +n: Nat, +rest: Nat) -> Nat:
  match hit:
    case True{}:
      n
    case False{}:
      rest

def no_at(ps: List<&2, Pr>, +i: Nat, +n: Nat) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          no_at.go(Nat.is_eq(pr_ix(a, b), i), n, no_at(t, i, 1n+n))

# every index from i, k of them, its rule's number or 0: dense, so that
# Bend makes the match a lookup table (a sparse one it makes a chain)
def at_cases(k: Nat, +i: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+r:
      "    case " ++ Nat.show(i) ++ ":\n      " ++ Nat.show(no_at(numbered(), i, 1n)) ++ "\n" ++ at_cases(r, 1n+i)

# a rule's arm: the payload test picking a variant, peeling, or the rule
def arm.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      "  match t:\n    case True{}:\n      " ++ call(R.rule(a, b, True{}), pname(a, b) ++ ".yes", checked(a, b)) ++
        "\n    case False{}:\n      " ++ call(R.rule(a, b, False{}), pname(a, b) ++ ".no", checked(a, b)) ++ "\n"
    case False{}:
      "  " ++ call(R.rule(a, b, False{}), pname(a, b), checked(a, b)) ++ "\n"

def arm.p(c: Bool, +d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      "  " ++ pname(a, b) ++ ".peeled(" ++ targ(True{}) ++ "P.peel_ctl(" ++ checked(a, b) ++ ", a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)\n"
    case False{}:
      arm.d(d, a, b)

def arm_params() -> String:
  tparam(True{}) ++ "+ka: U32, +t: Bool, h: P.H, " ++ common()

def arm_args() -> String:
  targ(True{}) ++ "ka, t, h, " ++ common_args()

def arms(ps: List<&2, Pr>, +n: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          "def rw.arm.r" ++ Nat.show(n) ++ "(" ++ arm_params() ++ ") -> R:\n" ++ arm.p(is_ctl_pair(a, b), differs(a, b), a, b) ++ "\n" ++
            arms(t, 1n+n)

def d_params() -> String:
  tparam(True{}) ++ "+ka: U32, +r: U32, +t: Bool, h: P.H, " ++ common()

def d_args() -> String:
  targ(True{}) ++ "ka, r, t, h, " ++ common_args()

def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+half(q)

def sub.one(one: Bool, +lo: Nat, +hi: Nat) -> String:
  match one:
    case True{}:
      "rw.arm.r" ++ Nat.show(lo) ++ "(" ++ arm_args() ++ ")"
    case False{}:
      "rw.t.r" ++ Nat.show(lo) ++ ".r" ++ Nat.show(hi) ++ "(" ++ d_args() ++ ")"

# the call reaching rules lo to hi - 1
def sub(+lo: Nat, +hi: Nat) -> String:
  sub.one(Nat.is_eq(Nat.sub(hi, lo), 1n), lo, hi)

# one node of the tree: rules lo to hi - 1, split at mid
def tree.node(+lo: Nat, +mid: Nat, +hi: Nat) -> String:
  "def rw.t.r" ++ Nat.show(lo) ++ ".r" ++ Nat.show(hi) ++ ".go(" ++ tparam(True{}) ++ "lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, " ++ common() ++ ") -> R:\n" ++
  "  match lt:\n    case True{}:\n      " ++ sub(lo, mid) ++ "\n    case False{}:\n      " ++ sub(mid, hi) ++ "\n\n" ++
  "def rw.t.r" ++ Nat.show(lo) ++ ".r" ++ Nat.show(hi) ++ "(" ++ d_params() ++ ") -> R:\n" ++
  "  rw.t.r" ++ Nat.show(lo) ++ ".r" ++ Nat.show(hi) ++ ".go(" ++ targ(True{}) ++ "U32.is_lt(r, " ++ Nat.show(mid) ++ "), ka, r, t, h, " ++ common_args() ++ ")\n\n"

type Rg is Data:
  Rg{+lo: Nat, +hi: Nat}

def tree.push(two: Bool, +lo: Nat, +mid: Nat, +hi: Nat, rest: List<&2, Rg>) -> List<&2, Rg>:
  match two:
    case True{}:
      Con{Rg{lo, mid}, Con{Rg{mid, hi}, rest}}
    case False{}:
      rest

def tree.text(two: Bool, +lo: Nat, +mid: Nat, +hi: Nat, +acc: String) -> String:
  match two:
    case True{}:
      tree.node(lo, mid, hi) ++ acc
    case False{}:
      acc

# a balanced tree of comparisons, its ranges on a worklist, each node's
# text put before those of the nodes taken before it, so callees come
# first; the fuel, twice the rules, bounds the steps
def tree(fuel: Nat, work: List<&2, Rg>, +acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match work:
        case Nil{}:
          acc
        case Con{r, t}:
          match r:
            case Rg{+lo, +hi}:
              tree(f, tree.push(Nat.is_ge(Nat.sub(hi, lo), 2n), lo, Nat.add(lo, half(Nat.sub(hi, lo))), hi, t),
                tree.text(Nat.is_ge(Nat.sub(hi, lo), 2n), lo, Nat.add(lo, half(Nat.sub(hi, lo))), hi, acc))

def hot.next(last: Bool, +m: Nat) -> String:
  match last:
    case True{}:
      sub(0n, Nat.add(n_cold(), 1n))
    case False{}:
      "rw.d.r" ++ Nat.show(1n+m) ++ "(" ++ targ(True{}) ++ "U32.is_eq(r, " ++ Nat.show(1n+m) ++ "), ka, r, t, h, " ++ common_args() ++ ")"

# the hot rules' tests, m down to the first, callees first
def hots(k: Nat, +m: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+r:
      hots(r, 1n+m) ++
      "def rw.d.r" ++ Nat.show(m) ++ "(" ++ tparam(True{}) ++ "hit: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, " ++ common() ++ ") -> R:\n" ++
      "  match hit:\n    case True{}:\n      rw.arm.r" ++ Nat.show(m) ++ "(" ++ arm_args() ++ ")\n    case False{}:\n      " ++
        hot.next(Nat.is_eq(m, n_rules()), m) ++ "\n\n"

def first_hot(+nh: Nat) -> String:
  match nh:
    case 0n:
      sub(0n, Nat.add(n_cold(), 1n))
    case 1n+r:
      "rw.d.r" ++ Nat.show(Nat.add(n_cold(), 1n)) ++ "(" ++ targ(True{}) ++ "U32.is_eq(r, " ++ Nat.show(Nat.add(n_cold(), 1n)) ++ "), ka, r, t, h, " ++ common_args() ++ ")"

def test_code.go(sl: Bool, vf: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match sl vf:
    case True{} _:
      "1"
    case False{} True{}:
      "2"
    case False{} False{}:
      "missing_payload_test_" ++ kname(a) ++ "_" ++ kname(b)

def test_code(+e: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  test_code.go(String.eq(e, "(h, P.same_lvl(ha, hb))"), String.eq(e, "P.val_is_fn(h, P.form(hb), P.fld(hb), pb)"), a, b)

def test_by.c(c: Bool, +n: Nat, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      "    case " ++ Nat.show(n) ++ ":\n      " ++ test_code(test_expr(a, b), a, b) ++ "\n"
    case False{}:
      "    case " ++ Nat.show(n) ++ ":\n      0\n"

def test_cases(ps: List<&2, Pr>, +n: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          test_by.c(differs(a, b) && Bool.not(is_ctl_pair(a, b)), n, a, b) ++ test_cases(t, 1n+n)

def dispatch() -> String:
  "# a kind's class, its row and column in the rule table: each base kind\n" ++
  "# its own, every code from the first operator's up one class, the\n" ++
  "# operators', whose rule picks the operation by the code inside its step\n" ++
  "# (header-kind-byte): a compare, where a table cost 2.3%; U32.is_lt, a\n" ++
  "# native comparison, where Base's U32.min splits the word into its bits\n" ++
  "def class.lt(lt: Bool, +k: U32) -> U32:\n  match lt:\n    case True{}:\n      k\n    case False{}:\n      " ++ Nat.show(n_base()) ++ "\n\n" ++
  "def class(+k: U32) -> U32:\n  class.lt(U32.is_lt(k, " ++ Nat.show(n_base()) ++ "), k)\n\n" ++
  "# the rule's number for A, negative principal, of class ca meeting B of\n" ++
  "# class cb, at ca times " ++ Nat.show(Nat.add(n_base(), 1n)) ++ " plus cb: 0 for a pair no rule rewrites\n" ++
  "def rule_at(+i: U32) -> U32:\n  match i:\n" ++ at_cases(Nat.mul(Nat.add(n_base(), 1n), Nat.add(n_base(), 1n)), 0n) ++ "    case _:\n      0\n\n" ++
  "def rule_no(+ka: U32, +kb: U32) -> U32:\n  rule_at(((class(ka) * " ++ Nat.show(Nat.add(n_base(), 1n)) ++ " : U32) + class(kb) : U32))\n\n" ++
  "# which payload test a rule's variants take: 0 none, 1 the levels' or the\n" ++
  "# fans' sites, 2 whether B's data is a builtin function\n" ++
  "def test_by(+r: U32) -> U32:\n  match r:\n    case 0:\n      0\n" ++ test_cases(numbered(), 1n) ++ "    case _:\n      0\n\n" ++
  "# the payload test that picks a rule's variant where the two differ (R.rule's\n" ++
  "# t; net.bend's rule_test), a template over the family and what follows\n" ++
  "# the rewrite, for a copy in each strategy's chain: shared, it has two\n" ++
  "# callers, and the compiler folds it into neither, which cost the eager\n" ++
  "# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested\n" ++
  "# after peeling instead (P.peel_ctl).\n" ++
  "def test.k(" ++ tparam(True{}) ++ "+k: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  match k:\n    case 1:\n      (h, P.same_lvl(ha, hb))\n    case 2:\n      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)\n    case _:\n      (h, False{})\n\n" ++
  "def test(" ++ tparam(True{}) ++ "+r: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  test.k(" ++ targ(True{}) ++ "test_by(r), h, ha, hb, pa, pb)\n\n"

def rewrites() -> String:
  "# the stuck pairs' arm, and each rule's\n" ++
  "def rw.arm.r0(" ++ arm_params() ++ ") -> R:\n  fin(P.err_if(U32.is_ne(ka, 8), h), st)\n\n" ++
  arms(numbered(), 1n) ++
  tree(Nat.mul(2n, Nat.add(n_cold(), 1n)), [Rg{0n, Nat.add(n_cold(), 1n)}], "") ++
  hots(List.length(&2, Pr, hot()), Nat.add(n_cold(), 1n)) ++
  "# the rewrite for A, negative principal, of kind ka, meeting B by rule r\n" ++
  "# (rule_no); t is the payload test; then `after`, at the external peers\n" ++
  "# where the rule may make an event\n" ++
  "def rewrite(" ++ d_params() ++ ") -> R:\n  " ++ first_hot(List.length(&2, Pr, hot())) ++ "\n"

def stuck_cases(ps: List<&2, Pr>, +n: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          "    case " ++ Nat.show(n) ++ ":\n      " ++ stuck_v(is_stuck(R.rule(a, b, True{})), is_stuck(R.rule(a, b, False{}))) ++ "\n" ++
            stuck_cases(t, 1n+n)

# a growth expression (grow_expr) as its table's code
def grow_code.go(t: Bool, ns: Bool, s: Bool, +x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match t ns s:
    case True{} _ _:
      "1"
    case False{} True{} _:
      "3"
    case False{} False{} True{}:
      "2"
    case False{} False{} False{}:
      x

def grow_code(+x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  grow_code.go(String.eq(x, "True{}"), String.eq(x, "Bool.not(P.same_lvl(ha, hb))"), String.eq(x, "P.same_lvl(ha, hb)"), x, a, b)

def grow_code.e(none: Bool, +x: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match none:
    case True{}:
      "0"
    case False{}:
      grow_code(x, a, b)

def grow_cases(ps: List<&2, Pr>, +n: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          "    case " ++ Nat.show(n) ++ ":\n      " ++
            grow_code.e(String.eq(grow_expr(grows_r(R.rule(a, b, True{})), grows_r(R.rule(a, b, False{})), a, b), ""),
              grow_expr(grows_r(R.rule(a, b, True{})), grows_r(R.rule(a, b, False{})), a, b), a, b) ++ "\n" ++ grow_cases(t, 1n+n)

def file() -> String:
  "import Base\n" ++
  "import ./kprim.bend as P\n" ++
  "import ./net.bend as N\n\n" ++
  "# The kernel's rewrites, generated from the rule table (spike/rules.bend)\n" ++
  "# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if\n" ++
  "# this file differs from what the generator writes. One family, generic\n" ++
  "# over what a strategy threads beside the net (knet.bend's Families): a\n" ++
  "# stack, on which each link a rewrite makes between two principal ports\n" ++
  "# is noted, or nothing.\n\n" ++
  tables() ++
  payloads() ++
  "# the level checks the rewrites below make, for the kernel's interpreter\n" ++
  "def check(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H:\n" ++
  "  match ka kb:\n" ++ checks_a(kinds()) ++ "    case _ _:\n      h\n\n" ++
  "# the most active pairs one rewrite makes (R.pairs_made, over the table):\n" ++
  "# a strategy's stack keeps room for that many before each rewrite (P.pop)\n" ++
  "def most_pairs() -> U32:\n  " ++ Nat.show(most_a(kinds(), 0n)) ++ "\n\n" ++
  dispatch() ++
  "# when the rule leaves A, negative principal, meeting B as it is (R.rule):\n" ++
  "# 0 never, 1 always, 2 when the payload test fails, 3 when it passes; by\n" ++
  "# the pair's rule (rule_no), a table, a pair no rule rewrites always\n" ++
  "def stuck_of(+r: U32) -> U32:\n  match r:\n    case 0:\n      1\n" ++ stuck_cases(numbered(), 1n) ++ "    case _:\n      1\n\n" ++
  "def stuck_by(+ka: U32, +kb: U32) -> U32:\n  stuck_of(rule_no(ka, kb))\n\n" ++
  "# does A, negative principal, meeting B make more nodes than the two it\n" ++
  "# frees? (R.rule; the pairs a two-stack strategy defers) By the pair's\n" ++
  "# rule, a table: 0 never, 1 always, 2 when the fans' levels agree, 3 when\n" ++
  "# they do not\n" ++
  "def grow_of(+r: U32) -> U32:\n  match r:\n    case 0:\n      0\n" ++ grow_cases(numbered(), 1n) ++ "    case _:\n      0\n\n" ++
  "def grows.k(+k: U32, +ha: U32, +hb: U32) -> Bool:\n  match k:\n    case 1:\n      True{}\n    case 2:\n      P.same_lvl(ha, hb)\n" ++
  "    case 3:\n      Bool.not(P.same_lvl(ha, hb))\n    case _:\n      False{}\n\n" ++
  "def grows(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:\n  grows.k(grow_of(rule_no(ka, kb)), ha, hb)\n\n" ++
  over_a(kinds(), True{}) ++
  events() ++
  rewrites()

def main() -> IO(Unit):
  IO.print(file())
