import Base
import ../rules.bend as R
import ../net.bend as N

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
  [R.KFree{}, R.KFn{}, R.KAp{}, R.KCopy{}, R.KMerge{}, R.KData{}, R.KEraN{}, R.KEraP{}, R.KRoot{}, R.KCall{}, R.KLift{}, R.KLiftC{}, R.KCopyL{}, R.KCopyR{}, R.KMergeL{}, R.KMergeR{}]

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

def code(+k: R.NodeKind) -> String:
  U32.show(N.kcode(k))

def is_data(k: R.NodeKind) -> Bool:
  match k:
    case R.KData{}:
      True{}
    case R.KCall{}:
      True{}
    case _:
      False{}

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
      "P.note(" ++ acc ++ ", " ++ u ++ ", " ++ v ++ ")"
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

# Two families of rewrites (heap-strategies.stack): the plain one, on the
# net alone, and the eager one (e), which takes a strategy's stack beside
# the net, notes on it each link it makes between two principal ports, in
# the table's order, and returns both (P.E). Its functions end in `.e`.

def stk_param(+e: Bool) -> String:
  match e:
    case True{}:
      "st: P.Stk, "
    case False{}:
      ""

def stk_arg(+e: Bool) -> String:
  match e:
    case True{}:
      "st, "
    case False{}:
      ""

def ret(+e: Bool) -> String:
  match e:
    case True{}:
      "P.E"
    case False{}:
      "P.H"

def sfx(+e: Bool) -> String:
  match e:
    case True{}:
      ".e"
    case False{}:
      ""

def common(+e: Bool) -> String:
  stk_param(e) ++ "+a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32"

def common_args(+e: Bool) -> String:
  stk_arg(e) ++ "a, b, ha, hb, pa, pb, e0, e1, e2, e3"

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
# A rule's rewrite is a template over `after`, what follows it (knet.bend's
# go.none, or the events' ev.settle), given the rule's sites: each
# strategy's copy of the rewrite chain then has its own copy of every
# rewrite beneath, each called once, which Bend folds into its caller
# (heap-strategies.erasure.kernel.parity). A rule with no site calls no
# `after`. An event's rewrite (w false) is no template: the events' loop
# alone calls it.

def after_ty(+e: Bool) -> String:
  ret(e) ++ " -> @+x:N.Ext -> " ++ ret(e)

def tparam(+e: Bool, w: Bool) -> String:
  match w:
    case True{}:
      "~after: " ++ after_ty(e) ++ ", "
    case False{}:
      ""

def targ(w: Bool) -> String:
  match w:
    case True{}:
      "~after, "
    case False{}:
      ""

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
def make_call(+e: Bool, +w: Bool, +name: String, +st: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_call(j, st) ++ hdr(k, s) ++ ", " ++ pword(s) ++ "), " ++ common_args(e) ++ made_args(j, 0n) ++ ")"
        case PAp{}:
          stepname(name, 1n+j) ++ ".pre(" ++ targ(w) ++ "P.apply(" ++ st ++ ", ha, pa, hb, pb), " ++ common_args(e) ++ made_args(j, 0n) ++ ")"
        case PDup{+isa}:
          stepname(name, 1n+j) ++ ".pre(" ++ targ(w) ++ "P.dup(" ++ st ++ ", P.form(h" ++ side(isa) ++ "), p" ++ side(isa) ++ "), " ++ common_args(e) ++ made_args(j, 0n) ++ ")"

# the step taking a computed value or a duplicate, making node j
def pre_fn(+e: Bool, +w: Bool, +name: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          ""
        case PAp{}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(" ++ tparam(e, w) ++ "r: P.H & P.PW, " ++ common(e) ++ made_params(j, 0n) ++ ") -> " ++ ret(e) ++ ":\n" ++
            "  (h, pw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_pw_call(j) ++ code(k) ++ ", pw), " ++ common_args(e) ++ made_args(j, 0n) ++ ")\n\n"
        case PDup{+isa}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(" ++ tparam(e, w) ++ "r: P.H & U32, " ++ common(e) ++ made_params(j, 0n) ++ ") -> " ++ ret(e) ++ ":\n" ++
            "  (h, +dw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(" ++ targ(w) ++ node_call(j, "h") ++ hdr(k, s) ++ ", dw), " ++ common_args(e) ++ made_args(j, 0n) ++ ")\n\n"

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
def finish.e(+e: Bool, +hs: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> String:
  match e:
    case True{}:
      "P.E{" ++ hs ++ ", " ++ notes(xs, ls, "st") ++ "}"
    case False{}:
      hs

def finish(+e: Bool, +w: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +st: String) -> String:
  finish.w(w && any_site(xs, ls), finish.e(e, fuses(xs, N.fuse_ends(xs, ls), links(xs, ls, st)), xs, ls), sites(xs, ls))

def step_body(+e: Bool, +w: Bool, last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      finish(e, w, xs, ls, "h")
    case False{}:
      make_call(e, w, name, "h", j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

def step_pre(+e: Bool, +w: Bool, last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      ""
    case False{}:
      pre_fn(e, w, name, j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

# step j (1 .. n), taking node j - 1
def step_fn(+e: Bool, +w: Bool, +name: String, +j: Nat, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  step_pre(e, w, Nat.is_ge(j, n), name, j, xs, a, b) ++
  "def " ++ stepname(name, j) ++ "(" ++ tparam(e, w) ++ "r: P.H & U32, " ++ common(e) ++ made_params(Nat.sub(j, 1n), 0n) ++ ") -> " ++ ret(e) ++ ":\n" ++
    "  (h, +n" ++ Nat.show(Nat.sub(j, 1n)) ++ ") = r\n" ++
    "  " ++ step_body(e, w, Nat.is_ge(j, n), name, j, xs, ls, a, b) ++ "\n\n"

# steps m down to 1
def steps(+e: Bool, +w: Bool, +m: Nat, +name: String, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match m:
    case 0n:
      ""
    case 1n+p:
      step_fn(e, w, name, m, n, xs, ls, a, b) ++ steps(e, w, p, name, n, xs, ls, a, b)

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

def entry(+e: Bool, +w: Bool, +name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match xs:
    case Nil{}:
      "def " ++ name ++ "(" ++ tparam(e, w) ++ "h: P.H, " ++ common(e) ++ ") -> " ++ ret(e) ++ ":\n" ++
        "  " ++ finish(e, w, xs, ls, start(xs, a, b)) ++ "\n\n"
    case Con{sp, t}:
      steps(e, w, List.length(&2, R.Spec, xs), name, List.length(&2, R.Spec, xs), xs, ls, a, b) ++
        pre_fn(e, w, name, 0n, sp, pre_of(sp, xs, 0n, a, b)) ++
        "def " ++ name ++ "(" ++ tparam(e, w) ++ "h: P.H, " ++ common(e) ++ ") -> " ++ ret(e) ++ ":\n" ++
        "  " ++ make_call(e, w, name, start(xs, a, b), 0n, sp, pre_of(sp, xs, 0n, a, b)) ++ "\n\n"

# a rule's functions, the first named `name`
def rule_fns(+e: Bool, +w: Bool, r: R.Rule, +name: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match r:
    case R.RStuck{}:
      ""
    case R.RWire{+xs, +ls}:
      entry(e, w, name, xs, ls, a, b)

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

# a stuck pair's state: the net, and in the eager family the stack too
def stuck_e(+e: Bool, +hs: String) -> String:
  match e:
    case True{}:
      "P.E{" ++ hs ++ ", st}"
    case False{}:
      hs

def call.s(+e: Bool, st: Bool, +name: String, +hs: String) -> String:
  match st:
    case True{}:
      stuck_e(e, "P.err_if(U32.is_ne(ka, 8), " ++ hs ++ ")")
    case False{}:
      name ++ "(~after, " ++ hs ++ ", " ++ common_args(e) ++ ")"

def call(+e: Bool, r: R.Rule, +name: String, +hs: String) -> String:
  call.s(e, is_stuck(r), name, hs)

# Pairs
# =====

def pname(+a: R.NodeKind, +b: R.NodeKind) -> String:
  "rw." ++ kname(a) ++ "." ++ kname(b)

# do the rule's two variants, for t true and false, differ?
def differs(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  Bool.not(String.eq(rule_fns(False{}, True{}, R.rule(a, b, True{}), "x", a, b), rule_fns(False{}, True{}, R.rule(a, b, False{}), "x", a, b)))

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

def peeled_fn(+e: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  "def " ++ pname(a, b) ++ ".peeled" ++ sfx(e) ++ "(" ++ tparam(e, True{}) ++ "r: P.Pl, " ++ stk_param(e) ++ "+a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> " ++ ret(e) ++ ":\n" ++
  "  match r:\n" ++
  "    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:\n" ++
  "      match t:\n" ++
  "        case True{}:\n" ++
  "          " ++ pname(a, b) ++ ".yes" ++ sfx(e) ++ "(~after, h, " ++ common_args(e) ++ ")\n" ++
  "        case False{}:\n" ++
  "          " ++ pname(a, b) ++ ".no" ++ sfx(e) ++ "(~after, h, " ++ common_args(e) ++ ")\n\n"

def peeled_fns(+e: Bool, c: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      peeled_fn(e, a, b)
    case False{}:
      ""

def pair_fns.d(+e: Bool, d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      rule_fns(e, True{}, R.rule(a, b, True{}), pname(a, b) ++ ".yes" ++ sfx(e), a, b) ++ rule_fns(e, True{}, R.rule(a, b, False{}), pname(a, b) ++ ".no" ++ sfx(e), a, b) ++
        peeled_fns(e, is_ctl_pair(a, b), a, b)
    case False{}:
      rule_fns(e, True{}, R.rule(a, b, False{}), pname(a, b) ++ sfx(e), a, b)

def pair_fns(+e: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_fns.d(e, differs(a, b), a, b)

def pair_case.d(+e: Bool, d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      match t:\n" ++
      "        case True{}:\n" ++
      "          " ++ call(e, R.rule(a, b, True{}), pname(a, b) ++ ".yes" ++ sfx(e), checked(a, b)) ++ "\n" ++
      "        case False{}:\n" ++
      "          " ++ call(e, R.rule(a, b, False{}), pname(a, b) ++ ".no" ++ sfx(e), checked(a, b)) ++ "\n"
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      " ++ call(e, R.rule(a, b, False{}), pname(a, b) ++ sfx(e), checked(a, b)) ++ "\n"

def pair_case.p(+e: Bool, c: Bool, +d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match c:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      " ++ pname(a, b) ++ ".peeled" ++ sfx(e) ++ "(~after, P.peel_ctl(" ++ checked(a, b) ++ ", a, b, ha, hb, pa, pb, e0, e2), " ++ stk_arg(e) ++ "a, b, ha, hb, e1, e3)\n"
    case False{}:
      pair_case.d(e, d, a, b)

def pair_case.s(+e: Bool, s: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match s:
    case True{}:
      ""
    case False{}:
      pair_case.p(e, is_ctl_pair(a, b), differs(a, b), a, b)

def pair_case(+e: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_case.s(e, both_stuck(a, b), a, b)

def pick(b: Bool, +x: String, +y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def over_b(+e: Bool, bs: List<&2, R.NodeKind>, +a: R.NodeKind, +fns: Bool) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      pick(fns, pair_fns(e, a, b), pair_case(e, a, b)) ++ over_b(e, t, a, fns)

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

# the payload test for one family (sfx): both from this one source
def tests(+e: Bool) -> String:
  "def test.k" ++ sfx(e) ++ "(" ++ tparam(e, True{}) ++ "+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  match ka kb:\n" ++ tests_a(kinds()) ++ "    case _ _:\n      (h, False{})\n\n" ++
  "def test" ++ sfx(e) ++ "(" ++ tparam(e, True{}) ++ "h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:\n" ++
  "  test.k" ++ sfx(e) ++ "(~after, P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)\n\n"

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

def over_a(+e: Bool, as: List<&2, R.NodeKind>, +fns: Bool) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      over_b(e, kinds(), a, fns) ++ over_a(e, t, fns)

def neg_str.b(b: Bool) -> String:
  match b:
    case True{}:
      "True{}"
    case False{}:
      "False{}"

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
  "# is the principal port negative? (R.port_pol)\n" ++
  "def kind_neg(+k: U32) -> Bool:\n  match k:\n" ++ tables.k(kinds(), True{}) ++ "    case _:\n      False{}\n\n"

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
      rule_fns(False{}, False{}, ev_rule(r), ev_name(a, p), a, b)
    case 1:
      rule_fns(True{}, False{}, ev_rule(r), ev_name(a, p) ++ ".e", a, b)
    case 2:
      ev_case(a, p, ev_name(a, p) ++ "(h, " ++ common_args(False{}) ++ ")")
    case _:
      ev_case(a, p, ev_name(a, p) ++ ".e(h, " ++ common_args(True{}) ++ ")")

# over kinds and ports with an event: f 0 the rewrites (plain), 1 (eager),
# 2 the dispatch's cases (plain), 3 (eager)
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
  ev_over(0, kinds()) ++ ev_over(1, kinds()) ++
  "# the event at port p of a node of kind ka, A, the eraser facing it B;\n" ++
  "# e0 the peer of A's principal, e1 of its other auxiliary port\n" ++
  "def event(+ka: U32, +p: U32, h: P.H, " ++ common(False{}) ++ ") -> P.H:\n" ++
  "  match ka p:\n" ++ ev_over(2, kinds()) ++ "    case _ _:\n      P.h_err(h)\n\n" ++
  "# the same, noting the pairs it makes on the strategy's stack\n" ++
  "def event.e(+ka: U32, +p: U32, h: P.H, " ++ common(True{}) ++ ") -> P.E:\n" ++
  "  match ka p:\n" ++ ev_over(3, kinds()) ++ "    case _ _:\n      P.E{P.h_err(h), st}\n\n"

def file() -> String:
  "import Base\n" ++
  "import ./kprim.bend as P\n" ++
  "import ./net.bend as N\n\n" ++
  "# The kernel's rewrites, generated from the rule table (spike/rules.bend)\n" ++
  "# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if\n" ++
  "# this file differs from what the generator writes. Two families: the\n" ++
  "# plain one on the net alone, and the eager one (`.e`), which notes on a\n" ++
  "# strategy's stack each link it makes between two principal ports.\n\n" ++
  tables() ++
  "# when the rule leaves A, negative principal, meeting B as it is (R.rule):\n" ++
  "# 0 never, 1 always, 2 when the payload test fails, 3 when it passes\n" ++
  "def stuck_by(+ka: U32, +kb: U32) -> U32:\n  match ka kb:\n" ++ stuck_a(kinds()) ++ "    case _ _:\n      1\n\n" ++
  "# the level checks the rewrites below make, for the kernel's interpreter\n" ++
  "def check(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H:\n" ++
  "  match ka kb:\n" ++ checks_a(kinds()) ++ "    case _ _:\n      h\n\n" ++
  "# the most active pairs one rewrite makes (R.pairs_made, over the table):\n" ++
  "# a strategy's stack keeps room for that many before each rewrite (P.pop)\n" ++
  "def most_pairs() -> U32:\n  " ++ Nat.show(most_a(kinds(), 0n)) ++ "\n\n" ++
  "# the payload test that picks a rule's variant where the two differ (R.rule's\n" ++
  "# t; net.bend's rule_test), a copy for each family and, a template over\n" ++
  "# what follows the rewrite, for each strategy's chain: shared, it has two\n" ++
  "# callers, and the compiler folds it into neither, which cost the eager\n" ++
  "# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested\n" ++
  "# after peeling instead (P.peel_ctl).\n" ++
  tests(False{}) ++ tests(True{}) ++
  "# does A, negative principal, meeting B make more nodes than the two it\n" ++
  "# frees? (R.rule; the pairs a two-stack strategy defers)\n" ++
  "def grows(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:\n  match ka kb:\n" ++ grows_a(kinds()) ++
  "    case _ _:\n      False{}\n\n" ++
  over_a(False{}, kinds(), True{}) ++
  over_a(True{}, kinds(), True{}) ++
  events() ++
  "# the rewrite for A, negative principal, meeting B; t is the payload test;\n" ++
  "# then `after`, at the external peers where the rule may make an event\n" ++
  "def rewrite(" ++ tparam(False{}, True{}) ++ "+ka: U32, +kb: U32, +t: Bool, h: P.H, " ++ common(False{}) ++ ") -> P.H:\n" ++
  "  match ka kb:\n" ++
  over_a(False{}, kinds(), False{}) ++
  "    case _ _:\n" ++
  "      P.err_if(U32.is_ne(ka, 8), h)\n\n" ++
  "# the same, noting the pairs it makes on the strategy's stack\n" ++
  "def rewrite.e(" ++ tparam(True{}, True{}) ++ "+ka: U32, +kb: U32, +t: Bool, h: P.H, " ++ common(True{}) ++ ") -> P.E:\n" ++
  "  match ka kb:\n" ++
  over_a(True{}, kinds(), False{}) ++
  "    case _ _:\n" ++
  "      P.E{P.err_if(U32.is_ne(ka, 8), h), st}\n"

def main() -> IO(Unit):
  IO.print(file())
