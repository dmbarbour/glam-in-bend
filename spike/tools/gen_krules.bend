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
  [R.KFree{}, R.KFn{}, R.KAp{}, R.KCopy{}, R.KMerge{}, R.KData{}, R.KEraN{}, R.KEraP{}, R.KRoot{}, R.KOp{}, R.KLift{}, R.KLiftC{}, R.KCopyL{}, R.KCopyR{}, R.KMergeL{}, R.KMergeR{}, R.KDOp{}, R.KFnD{}]

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
    case R.KOp{}:
      "Op"
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
    case R.KDOp{}:
      "DOp"
    case R.KFnD{}:
      "FnD"

def code(+k: R.NodeKind) -> String:
  U32.show(N.kcode(k))

# what a kind's payload word holds, by the model's table (R.holds)
def is_data(k: R.NodeKind) -> Bool:
  R.holds_value(R.holds(k))

def has_pay(k: R.NodeKind) -> Bool:
  R.holds_some(R.holds(k))

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

# a link, by its ends: between two new nodes' ports P.link; from a new
# node's port to an external peer, which may be static, with no link word
# to write back to (kprim.bend's Static links), P.link_x, the new port
# first; between two external peers P.link_xx
def link_call(+xs: List<&2, R.Spec>, u: R.End, v: R.End, +acc: String) -> String:
  match u v:
    case R.New{j, p} R.New{k, q}:
      "P.link(" ++ acc ++ ", " ++ new_end(j, p) ++ ", " ++ new_end(k, q) ++ ")"
    case R.New{j, p} R.Ext{i}:
      "P.link_x(" ++ acc ++ ", " ++ new_end(j, p) ++ ", e" ++ Nat.show(i) ++ ")"
    case R.Ext{i} R.New{j, p}:
      "P.link_x(" ++ acc ++ ", " ++ new_end(j, p) ++ ", e" ++ Nat.show(i) ++ ")"
    case R.Ext{i} R.Ext{k}:
      "P.link_xx(" ++ acc ++ ", e" ++ Nat.show(i) ++ ", e" ++ Nat.show(k) ++ ")"

def links(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{u, v}, t}:
      links(xs, t, link_call(xs, u, v, acc))

def note_if(c: Bool, +acc: String, +u: String, +v: String) -> String:
  match c:
    case True{}:
      "note(" ++ acc ++ ", " ++ u ++ ", " ++ v ++ ")"
    case False{}:
      acc

# a note's ends: a new node's first, which is never static; of two
# external peers, either of which may be static (P.note), the one that is
# not (P.site), then the other
def note_x(u: R.End, v: R.End) -> String:
  match u v:
    case R.Ext{i} R.New{j, p}:
      new_end(j, p)
    case R.Ext{i} R.Ext{k}:
      "P.site(e" ++ Nat.show(i) ++ ", e" ++ Nat.show(k) ++ ")"
    case R.New{j, p} _:
      new_end(j, p)

def note_y(+xs: List<&2, R.Spec>, u: R.End, v: R.End) -> String:
  match u v:
    case R.Ext{i} R.New{j, p}:
      "e" ++ Nat.show(i)
    case _ _:
      end(xs, v)

# the eager family's notes: each link that may join two principal ports
# (R.may_pri, as R.pairs_made counts them), in the order links makes them
def notes(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{+u, +v}, t}:
      notes(xs, t, note_if(R.may_pri(u) && R.may_pri(v), acc, note_x(u, v), note_y(xs, u, v)))

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
      "~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, ~erased: R -> @+x:N.Ext -> R, "
    case False{}:
      "~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, "

def targ(w: Bool) -> String:
  match w:
    case True{}:
      "~S, ~R, ~note, ~fin, ~after, ~erased, "
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

# a rule that makes erasers, static, ends by `erased` where others end by
# `after`: the events where its statics land, run in every strategy, so
# that none is tested for after a rewrite that writes no static
# (`.links.propagate.writers`, erasure-at-write)
def finish.n(w: Bool, +x: String, +ss: String) -> String:
  match w:
    case True{}:
      "erased(" ++ x ++ ", " ++ ss ++ ")"
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

def node_call_h.go(reuse: Bool, +j: Nat, +st: String) -> String:
  match reuse:
    case True{}:
      "P.renode.h(" ++ st ++ ", " ++ slot.go(Nat.is_eq(j, 0n), j) ++ ", "
    case False{}:
      "P.node.h(" ++ st ++ ", "

# node j's call where its kind has three ports: its header alone, its word
# 3 port 2's link, which the rewrite writes (P.node.h)
def node_call_h(+j: Nat, +st: String) -> String:
  node_call_h.go(Nat.is_lt(j, 2n), j, st)

def make.node(three: Bool, +j: Nat, +st: String, +k: R.NodeKind, +s: R.Src) -> String:
  match three:
    case True{}:
      node_call_h(j, st) ++ hdr(k, s) ++ ")"
    case False{}:
      node_call(j, st) ++ hdr(k, s) ++ ", " ++ pword(s) ++ ")"

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
          stepname(name, 1n+j) ++ "(" ++ targ(w) ++ make.node(Nat.is_eq(R.arity(k), 3n), j, st, k, s) ++ ", " ++ common_args() ++ made_args(j, 0n) ++ ")"
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
# eraser's principal, or a new dead call's (is_ev_b); one facing a new
# node's auxiliary port at which such a node makes an event; one end of each wire joining two external peers,
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

def ev_ports() -> List<&2, Nat>:
  [1n, 2n]

def is_ev_b.p(ps: List<&2, Nat>, +a: R.NodeKind, +b: R.NodeKind) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{+p, t}:
      Bool.not(is_stuck(R.event(a, b, p))) || is_ev_b.p(t, a, b)

def is_ev_b.a(as: List<&2, R.NodeKind>, +b: R.NodeKind) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{+a, t}:
      is_ev_b.p(ev_ports(), a, b) || is_ev_b.a(t, b)

# may a node of kind b be B, its principal facing A's auxiliary port, in
# some event: an eraser, or one R.event names besides, a dead call
# (heap-strategies.erasure.deadcall.chain)
def is_ev_b(+b: R.NodeKind) -> Bool:
  is_eraser(b) || is_ev_b.a(kinds(), b)

def ev_bs.hit(hit: Bool, +k: R.NodeKind, rest: List<&2, R.NodeKind>) -> List<&2, R.NodeKind>:
  match hit:
    case True{}:
      Con{k, rest}
    case False{}:
      rest

# the kinds B may be, the erasers among them or not
def ev_bs.go(+erasers: Bool, ks: List<&2, R.NodeKind>) -> List<&2, R.NodeKind>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, t}:
      ev_bs.hit(is_ev_b(k) && (erasers || Bool.not(is_eraser(k))), k, ev_bs.go(erasers, t))

def ev_bs() -> List<&2, R.NodeKind>:
  ev_bs.go(True{}, kinds())

# the kinds besides the erasers B may be
def ev_others() -> List<&2, R.NodeKind>:
  ev_bs.go(False{}, kinds())

def ev_port(+k: R.NodeKind, +p: Nat) -> Bool:
  Maybe.is_some(&2, R.NodeKind, ev_eraser(ev_bs(), k, p))

def site.end(+xs: List<&2, R.Spec>, e: R.End, +i: Nat) -> Bool:
  match e:
    case R.New{+j, +p}:
      match p:
        case 0n:
          is_ev_b(spec_kind(spec_at(xs, j)))
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

# the end the rule links external peer i to
def facing(+xs: List<&2, R.Spec>, m: Maybe<&2, R.End>) -> String:
  match m:
    case Some{e}:
      end(xs, e)
    case None{}:
      "P.nil()"

# a site: external peer i, or where it is static, no node to look at,
# the end the rule linked it to (P.site)
def site.s(b: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +i: Nat) -> String:
  match b:
    case True{}:
      "P.site(e" ++ Nat.show(i) ++ ", " ++ facing(xs, R.lf.peer(ls, R.Ext{i})) ++ ")"
    case False{}:
      "P.nil()"

def any_site(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> Bool:
  site(xs, ls, 0n) || site(xs, ls, 1n) || site(xs, ls, 2n) || site(xs, ls, 3n)

def sites(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> String:
  "N.Ext4{" ++ site.s(site(xs, ls, 0n), xs, ls, 0n) ++ ", " ++ site.s(site(xs, ls, 1n), xs, ls, 1n) ++ ", " ++
    site.s(site(xs, ls, 2n), xs, ls, 2n) ++ ", " ++ site.s(site(xs, ls, 3n), xs, ls, 3n) ++ "}"

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

def free.one(+w: Bool, one: Bool) -> String:
  match w one:
    case True{} True{}:
      "P.free(h, b)"
    case False{} True{}:
      "P.free_b(h, b)"
    case _ False{}:
      "h"

def free.two(w: Bool) -> String:
  match w:
    case True{}:
      "P.fresh2(h, a, b)"
    case False{}:
      "P.free(P.free_b(h, b), a)"

# the redex's slots no new node takes, freed: both for a rule making
# none, b's for one making one. An event's B may be static, with no
# node to free (P.free_b)
def free_of(+w: Bool, +n: Nat) -> String:
  match n:
    case 0n:
      free.two(w)
    case 1n+p:
      free.one(w, Nat.is_eq(p, 0n))

# the state after freeing the redex: a data payload no new node uses,
# dropped
def start(+w: Bool, +xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  drop_if(is_data(b) && Nat.is_eq(uses(xs, False{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
    drop_if(is_data(a) && Nat.is_eq(uses(xs, True{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
      free_of(w, List.length(&2, R.Spec, xs)), True{}), False{})

# Native erasers (heap-strategies.erasure.load.cycle.walk.directed.
# dead-kinds.links.native): a rule whose new nodes are all erasers, each
# facing an external peer or another of them (law erasers_native), makes
# them static, no node: both of the redex's slots freed, a static put in
# the link word of the peer each faces (P.put_st), two facing a meeting,
# noted as a pair of allocated erasers would be
# (static-links-count-as-nodes). Events keep their eraser in the node's
# own slot: a pair the node is in keeps its place on a strategy's stack
# by that node.

def st_name(k: R.NodeKind) -> String:
  "P.era()"

# an end as a native rule names it: a new eraser by its static
def nv.end(+xs: List<&2, R.Spec>, e: R.End) -> String:
  match e:
    case R.Ext{i}:
      "e" ++ Nat.show(i)
    case R.New{+j, p}:
      st_name(spec_kind(spec_at(xs, j)))

def nv.link(+xs: List<&2, R.Spec>, u: R.End, v: R.End, +acc: String) -> String:
  match u v:
    case R.Ext{i} R.Ext{k}:
      "P.link_xx(" ++ acc ++ ", e" ++ Nat.show(i) ++ ", e" ++ Nat.show(k) ++ ")"
    case R.Ext{i} R.New{+j, p}:
      "P.put_st(" ++ acc ++ ", e" ++ Nat.show(i) ++ ", " ++ st_name(spec_kind(spec_at(xs, j))) ++ ")"
    case R.New{+j, p} R.Ext{i}:
      "P.put_st(" ++ acc ++ ", e" ++ Nat.show(i) ++ ", " ++ st_name(spec_kind(spec_at(xs, j))) ++ ")"
    case R.New{j, p} R.New{k, q}:
      acc

def nv.links(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{u, v}, t}:
      nv.links(xs, t, nv.link(xs, u, v, acc))

# a note's ends in a native rule: of an external peer and what faces it,
# the peer unless it is static (P.site); of two statics, either
def nv.note_x(+xs: List<&2, R.Spec>, u: R.End, v: R.End) -> String:
  match u v:
    case R.Ext{i} _:
      "P.site(e" ++ Nat.show(i) ++ ", " ++ nv.end(xs, v) ++ ")"
    case R.New{j, p} R.Ext{i}:
      "P.site(e" ++ Nat.show(i) ++ ", " ++ nv.end(xs, u) ++ ")"
    case R.New{j, p} R.New{k, q}:
      nv.end(xs, u)

def nv.note_y(+xs: List<&2, R.Spec>, u: R.End, v: R.End) -> String:
  match u v:
    case R.New{j, p} R.Ext{i}:
      nv.end(xs, u)
    case _ _:
      nv.end(xs, v)

def nv.notes(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{+u, +v}, t}:
      nv.notes(xs, t, note_if(R.may_pri(u) && R.may_pri(v), acc, nv.note_x(xs, u, v), nv.note_y(xs, u, v)))

def nv.fuses(+xs: List<&2, R.Spec>, es: List<&2, R.End>, +acc: String) -> String:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      nv.fuses(xs, t, "P.fuse(" ++ acc ++ ", " ++ nv.end(xs, e) ++ ")")

def nv.site(m: Maybe<&2, R.End>, +xs: List<&2, R.Spec>) -> String:
  match m:
    case Some{e}:
      nv.end(xs, e)
    case None{}:
      "P.nil()"

def nv.site.s(b: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +i: Nat) -> String:
  match b:
    case True{}:
      "P.site(e" ++ Nat.show(i) ++ ", " ++ nv.site(R.lf.peer(ls, R.Ext{i}), xs) ++ ")"
    case False{}:
      "P.nil()"

def nv.sites(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>) -> String:
  "N.Ext4{" ++ nv.site.s(site(xs, ls, 0n), xs, ls, 0n) ++ ", " ++ nv.site.s(site(xs, ls, 1n), xs, ls, 1n) ++ ", " ++
    nv.site.s(site(xs, ls, 2n), xs, ls, 2n) ++ ", " ++ nv.site.s(site(xs, ls, 3n), xs, ls, 3n) ++ "}"

def nv.finish(+xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +st: String) -> String:
  finish.n(any_site(xs, ls), "fin(" ++ nv.fuses(xs, N.fuse_ends(xs, ls), nv.links(xs, ls, st)) ++ ", " ++ nv.notes(xs, ls, "st") ++ ")", nv.sites(xs, ls))

def entry.k(+w: Bool, +name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match xs:
    case Nil{}:
      "def " ++ name ++ "(" ++ tparam(w) ++ "h: P.H, " ++ common() ++ ") -> " ++ ret(w) ++ ":\n" ++
        "  " ++ finish(w, xs, ls, start(w, xs, a, b)) ++ "\n\n"
    case Con{sp, t}:
      steps(w, List.length(&2, R.Spec, xs), name, List.length(&2, R.Spec, xs), xs, ls, a, b) ++
        pre_fn(w, name, 0n, sp, pre_of(sp, xs, 0n, a, b)) ++
        "def " ++ name ++ "(" ++ tparam(w) ++ "h: P.H, " ++ common() ++ ") -> " ++ ret(w) ++ ":\n" ++
        "  " ++ make_call(w, name, start(w, xs, a, b), 0n, sp, pre_of(sp, xs, 0n, a, b)) ++ "\n\n"

def entry.go(+native: Bool, +w: Bool, +name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match native:
    case True{}:
      "def " ++ name ++ "(" ++ tparam(w) ++ "h: P.H, " ++ common() ++ ") -> " ++ ret(w) ++ ":\n" ++
        "  " ++ nv.finish(xs, ls, start(w, [], a, b)) ++ "\n\n"
    case False{}:
      entry.k(w, name, xs, ls, a, b)

def entry(+w: Bool, +name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  entry.go(w && R.nv.any(xs), w, name, xs, ls, a, b)

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

def check_expr.raw(+a: R.NodeKind, +b: R.NodeKind) -> String:
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

def check_expr.sel(b: Bool, +x: String, +y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def check_expr.go(listed: Bool, +raw: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match listed:
    case True{}:
      check_expr.sel(String.eq(raw, ""), "level_check_missing_" ++ kname(a) ++ "_" ++ kname(b), raw)
    case False{}:
      check_expr.sel(String.eq(raw, ""), "", "level_check_unlisted_" ++ kname(a) ++ "_" ++ kname(b))

# the pair's level check, where the model lists one (R.checks_levels, whose
# kinds law reads_leveled holds leveled): a check written here and not
# listed there, or listed and not written, names what does not exist
def check_expr.full(+a: R.NodeKind, +b: R.NodeKind) -> String:
  check_expr.go(R.checks_levels(a, b), check_expr.raw(a, b), a, b)

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

def pick.n(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

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

# the ports the collection's walk follows from a node of kind k, its
# inputs (R.walk_first, R.walk_second; law walk_follows_inputs), packed
# as the first plus 4 times the second, 3 for none
def dir_k(+k: R.NodeKind) -> U32:
  (U32.from_nat(R.walk_first(k)) + (4 * U32.from_nat(R.walk_second(k)) : U32) : U32)

def tables.d(ks: List<&2, R.NodeKind>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      "    case " ++ code(k) ++ ":\n      " ++ U32.show(dir_k(k)) ++ "\n" ++ tables.d(t)

def oth.has(+k: R.NodeKind) -> Bool:
  Bool.not(Nat.is_eq(R.walk_other(k, 0n), 3n)) || Bool.not(Nat.is_eq(R.walk_other(k, 1n), 3n)) || Bool.not(Nat.is_eq(R.walk_other(k, 2n), 3n))

def oth.p(+k: R.NodeKind, +p: Nat) -> Nat:
  pick.n(R.is_output(k, p), p, 0n)

# a kind's two outputs' sum, so that the other of output p is the sum less
# p, arithmetic where a nested match cost the walk about 1.5 instructions
# a node (gcbench run 229)
def oth.sum(+k: R.NodeKind) -> Nat:
  Nat.add(oth.p(k, 0n), Nat.add(oth.p(k, 1n), oth.p(k, 2n)))

def tables.o(ks: List<&2, R.NodeKind>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      pick(oth.has(k), "    case " ++ code(k) ++ ":\n      (" ++ Nat.show(oth.sum(k)) ++ " - p : U32)\n", "") ++ tables.o(t)

# ports and principal polarity by kind code (R.arity, R.port_pol)
def tables() -> String:
  "# ports by kind code (R.arity)\n" ++
  "def kind_arity(+k: U32) -> U32:\n  match k:\n" ++ tables.k(kinds(), False{}) ++ "    case _:\n      0\n\n" ++
  "# 1 where the principal port is negative (R.port_pol): a table, where a\n" ++
  "# match whose arms are constructors would be a chain\n" ++
  "def kind_neg.n(+k: U32) -> U32:\n  match k:\n" ++ tables.k(kinds(), True{}) ++ "    case _:\n      0\n\n" ++
  "def kind_neg(+k: U32) -> Bool:\n  U32.is_eq(kind_neg.n(k), 1)\n\n" ++
  "# the ports the collection's walk follows, a node's inputs (R.walk_first,\n" ++
  "# R.walk_second): the first plus 4 times the second, 3 for none\n" ++
  "def kind_dir(+k: U32) -> U32:\n  match k:\n" ++ tables.d(kinds()) ++ "    case _:\n      15\n\n" ++
  "# the other output of a node of kind k entered by its output p, where\n" ++
  "# it has two, 3 where none (R.walk_other; law two_outputs): the two\n" ++
  "# outputs' sum less p, p an output, as the walk enters only by one (law\n" ++
  "# walk_follows_inputs)\n" ++
  "def walk_oth(+k: U32, +p: U32) -> U32:\n  match k:\n" ++ tables.o(kinds()) ++ "    case _:\n      3\n\n"

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

# an event whose B is no eraser, named for it too
def ev_name.b(+a: R.NodeKind, +p: Nat, +b: R.NodeKind) -> String:
  ev_name(a, p) ++ "." ++ kname(b)

def first_kind(xs: List<&2, R.Spec>) -> R.NodeKind:
  match xs:
    case Nil{}:
      R.KFree{}
    case Con{R.Spec{+k, s}, t}:
      k

# a dispatch case: B's kind kb, for an eraser any
def ev_case(+a: R.NodeKind, +p: Nat, +kb: String, +body: String) -> String:
  "    case " ++ code(a) ++ " " ++ Nat.show(p) ++ " " ++ kb ++ ":\n      " ++ body ++ "\n"

def ev_one.f(+f: U32, r: R.Rule, +a: R.NodeKind, +b: R.NodeKind, +p: Nat) -> String:
  match f:
    case 0:
      rule_fns(False{}, ev_rule(r), ev_name(a, p), a, b)
    case _:
      ev_case(a, p, "_", ev_name(a, p) ++ "(" ++ targ(False{}) ++ "h, " ++ common_args() ++ ")")

def ev_other.f(+f: U32, r: R.Rule, +a: R.NodeKind, +b: R.NodeKind, +p: Nat) -> String:
  match f:
    case 0:
      rule_fns(False{}, ev_rule(r), ev_name.b(a, p, b), a, b)
    case 1:
      ev_case(a, p, code(b), ev_name.b(a, p, b) ++ "(" ++ targ(False{}) ++ "h, " ++ common_args() ++ ")")
    case _:
      ev_case(a, p, code(b), "True{}")

def ev_other.hit(stuck: Bool, +f: U32, r: R.Rule, +a: R.NodeKind, +b: R.NodeKind, +p: Nat) -> String:
  match stuck:
    case True{}:
      ""
    case False{}:
      ev_other.f(f, r, a, b, p)

# the events at port p of kind a whose B is no eraser: f 0 the rewrites,
# 1 the dispatch's cases, 2 ev_also's; before the eraser's, whose case
# takes any B
def ev_others_one(+f: U32, bs: List<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      ev_other.hit(is_stuck(R.event(a, b, p)), f, R.event(a, b, p), a, b, p) ++ ev_others_one(f, t, a, p)

def ev_one(+f: U32, m: Maybe<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat) -> String:
  match m:
    case None{}:
      ""
    case Some{+b}:
      ev_one.f(f, R.event(a, b, p), a, b, p)

# over kinds and ports with an event: f 0 the rewrites, 1 the dispatch's
# cases, 2 ev_also's (the erasers' none)
def ev_one.e(+f: U32, m: Maybe<&2, R.NodeKind>, +a: R.NodeKind, +p: Nat) -> String:
  match f:
    case 2:
      ""
    case _:
      ev_one(f, m, a, p)

def ev_over_p(+f: U32, ps: List<&2, Nat>, +a: R.NodeKind) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, t}:
      ev_others_one(f, ev_others(), a, p) ++ ev_one.e(f, ev_eraser(eraser_codes(), a, p), a, p) ++ ev_over_p(f, t, a)

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
      ev_most_p(t, a, ev_most_b(ev_bs(), a, p, m))

# the most active pairs one event makes
def ev_most(as: List<&2, R.NodeKind>, +m: Nat) -> Nat:
  match as:
    case Nil{}:
      m
    case Con{+a, t}:
      ev_most(t, ev_most_p(ev_ports(), a, m))

def spec_k(xs: List<&2, R.Spec>, +j: Nat) -> R.NodeKind:
  spec_kind(spec_at(xs, j))

# an eraser's principal, or a dead call's, new node j port p, facing an
# auxiliary port of new node k, port q, at which it makes an event
def inner_ev.dir(+xs: List<&2, R.Spec>, +j: Nat, +p: Nat, +k: Nat, +q: Nat) -> Bool:
  is_ev_b(spec_k(xs, j)) && Nat.is_eq(p, 0n) && Nat.is_ne(q, 0n) && Bool.not(is_stuck(R.event(spec_k(xs, k), spec_k(xs, j), q)))

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

def ev_end.os(bs: List<&2, R.NodeKind>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      " || U32.is_eq(k, " ++ code(b) ++ ")" ++ ev_end.os(t)

def ev_only.hit(bad: Bool, +a: R.NodeKind, +p: Nat) -> String:
  match bad:
    case True{}:
      " || ev_only_" ++ kname(a) ++ "_p" ++ Nat.show(p)
    case False{}:
      ""

def ev_only.p(ps: List<&2, Nat>, +a: R.NodeKind) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, t}:
      ev_only.hit(Bool.not(Maybe.is_some(&2, R.NodeKind, ev_eraser(eraser_codes(), a, p))) && Maybe.is_some(&2, R.NodeKind, ev_eraser(ev_others(), a, p)), a, p) ++ ev_only.p(t, a)

# an auxiliary port at which some kind besides the erasers makes an event
# and no eraser does: ev_end would not look at it
def ev_only(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      ev_only.p(ev_ports(), a) ++ ev_only(t)

def ev_b_held.hit(held: Bool, +b: R.NodeKind) -> String:
  match held:
    case True{}:
      " + event_b_holds_" ++ kname(b)
    case False{}:
      ""

# a kind B may be that holds a payload: the kernel reads no word of B's
# (knet.bend's ev.run), so this names what does not exist
def ev_b_held(bs: List<&2, R.NodeKind>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      ev_b_held.hit(has_pay(b), b) ++ ev_b_held(t)

def events() -> String:
  "# Events (R.event)\n\n" ++
  "# rules linking two of their own new nodes into an event: none, or this\n" ++
  "# names what does not exist\n" ++
  "def inner_events() -> U32:\n  0" ++ inner_ev_a(kinds()) ++ ev_b_held(ev_bs()) ++ "\n\n" ++
  "# the eraser kind making an event at port p of kind k, 0 for none: two\n" ++
  "# bits a port (0 none, 1 EraN, 2 EraP), eight a kind, four kinds a word;\n" ++
  "# a kind past 15 makes none (law events_fit_header)\n" ++
  "def ev_word(+w: U32) -> U32:\n  match w:\n" ++
  "    case 0:\n      " ++ U32.show(ev_word_k(kinds(), 0, 0)) ++ "\n" ++
  "    case 1:\n      " ++ U32.show(ev_word_k(kinds(), 1, 0)) ++ "\n" ++
  "    case 2:\n      " ++ U32.show(ev_word_k(kinds(), 2, 0)) ++ "\n" ++
  "    case 3:\n      " ++ U32.show(ev_word_k(kinds(), 3, 0)) ++ "\n" ++
  "    case _:\n      0\n\n" ++
  "def ev_by.c(+c: U32) -> U32:\n  match c:\n    case 0:\n      0\n    case _:\n      (c + 5 : U32)\n\n" ++
  "def ev_by(+k: U32, +p: U32) -> U32:\n" ++
  "  ev_by.c(((ev_word((k >> 2n : U32)) >> U32.to_nat((((k .&. 3 : U32) * 8 : U32) + (p * 2 : U32) : U32)) : U32) .&. 3 : U32))\n\n" ++
  "# whether B, of kind kb, no eraser, makes the event at port p of kind\n" ++
  "# k: a dead call, a call's output feeding it (deadcall.chain)\n" ++
  "def ev_also(+k: U32, +p: U32, +kb: U32) -> Bool:\n  match k p kb:\n" ++ ev_over(2, kinds()) ++ "    case _ _ _:\n      False{}\n\n" ++
  "# may port p of kind k be one end of an event: an eraser's principal or a\n" ++
  "# dead call's, or an auxiliary port some eraser makes an event at; one\n" ++
  "# where only another kind makes one names what does not exist\n" ++
  "def ev_end(+k: U32, +p: U32) -> Bool:\n" ++
  "  (U32.is_eq(p, 0) && (U32.is_eq((k .|. 1 : U32), 7)" ++ ev_end.os(ev_others()) ++ ")) || U32.is_ne(ev_by(k, p), 0)" ++ ev_only(kinds()) ++ "\n\n" ++

  "# the most active pairs one event makes\n" ++
  "def ev_most() -> U32:\n  " ++ Nat.show(ev_most(kinds(), 0n)) ++ "\n\n" ++
  ev_over(0, kinds()) ++
  "# the event at port p of a node of kind ka, A, B of kind kb facing it,\n" ++
  "# an eraser or a dead call; e0 the peer of A's principal, e1 of its other\n" ++
  "# auxiliary port; the net and the family's state, the pairs it makes\n" ++
  "# noted\n" ++
  "def event(" ++ tparam(False{}) ++ "+ka: U32, +p: U32, +kb: U32, h: P.H, " ++ common() ++ ") -> P.H & S:\n" ++
  "  match ka p kb:\n" ++ ev_over(1, kinds()) ++ "    case _ _ _:\n      (P.h_err(h), st)\n\n"

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
  [Pr{R.KOp{}, R.KMerge{}}, Pr{R.KOp{}, R.KData{}}, Pr{R.KOp{}, R.KLiftC{}}, Pr{R.KLift{}, R.KLiftC{}}]

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

# Collecting (heap-strategies.cascade.nongrow; heap-strategies.erasure.
# load): may a collection reduce A meeting B? Where the rule is never
# stuck, makes at most the two nodes it frees and applies no builtin, the
# pair is no need for a lazy value, and the rule leaves fewer ports than
# the pair had, as an event does (law events_shrink), so that a
# collection's cascade of rewrites and events ends within the net's ports
# (heap-strategies.erasure.load.cycle.shrink): erasures, annihilations,
# beta at one level, copies of data, the events with them; controls
# passing, which leave as many ports as they take, are demand's. A copy
# of a table entry adds one to the table, which the copy node it consumes
# bounds (the maintainer, 2026-11-01; heap-strategies.erasure.load.cycle).
# Where the variants differ, the header test the pair's payload test is
# (P.same_lvl) decides; with no such test, a pair named in
# collect_untested is left uncollected, and any other stops the
# generator, naming the test it lacks.

# an application or an operator meeting data, which may be a need for a
# lazy value only the table tells (kstrat.bend's may_need): never collected
def may_need_k(a: R.NodeKind, b: R.NodeKind) -> Bool:
  match a b:
    case R.KAp{} R.KData{}:
      True{}
    case R.KOp{} R.KData{}:
      True{}
    case _ _:
      False{}

def collect_r.r(r: R.Rule, +a: R.NodeKind, +b: R.NodeKind) -> Bool:
  match r:
    case R.RWire{+xs, ls}:
      Nat.is_le(List.length(&2, R.Spec, xs), 2n) && Bool.not(has_apply(xs)) &&
        Nat.is_lt(R.ports_of(xs), Nat.add(R.arity(a), R.arity(b)))
    case R.RStuck{}:
      False{}

def collect_r(+a: R.NodeKind, +b: R.NodeKind, r: R.Rule) -> Bool:
  Bool.not(may_need_k(a, b)) && collect_r.r(r, a, b)

# the pairs whose payload test is the header test P.same_lvl
def collect_test.full(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  match a b:
    case R.KCopy{} R.KMerge{}:
      True{}
    case R.KAp{} R.KFn{}:
      True{}
    case _ _:
      False{}

def collect_test(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  collect_test.full(R.lf.full(a), R.lf.full(b))

# the pairs collectable in one variant only that no header test tells
# apart, left uncollected until a collection can test them, each named so
# that none is forgotten: a level control meeting its co-control, which
# annihilates where their indexes agree, an agreement read from their
# payloads after peeling a fused run (P.Pl), which the header test cannot
# see (heap-strategies.erasure.load.cycle.shrink.untested)
def collect_untested(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  match a b:
    case R.KLift{} R.KLiftC{}:
      True{}
    case _ _:
      False{}

def collect_code.untested(+tested: Bool, +code: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match tested:
    case True{}:
      code
    case False{}:
      pick(collect_untested(a, b), "0", "missing_collect_test_" ++ kname(a) ++ "_" ++ kname(b))

def collect_code.go(+cy: Bool, +cn: Bool, +tested: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match cy cn:
    case True{} True{}:
      "1"
    case False{} False{}:
      "0"
    case True{} False{}:
      collect_code.untested(tested, "2", a, b)
    case False{} True{}:
      collect_code.untested(tested, "3", a, b)

def collect_code(+a: R.NodeKind, +b: R.NodeKind) -> String:
  collect_code.go(collect_r(a, b, R.rule(a, b, True{})), collect_r(a, b, R.rule(a, b, False{})), collect_test(a, b), a, b)

def collect_cases(ps: List<&2, Pr>, +n: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case Pr{+a, +b}:
          "    case " ++ Nat.show(n) ++ ":\n      " ++ collect_code(a, b) ++ "\n" ++ collect_cases(t, 1n+n)

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

# A meeting the identity (heap-strategies.erasure.load.cycle.walk.
# directed.dataflow.walk.loops): a function whose body is its variable,
# its ports 1 and 2 wired to each other, for which the kernel took the
# interpreted table. Its rule with that loop resolved ahead (R.rule_id,
# law identity_resolved) is generated as any rule is, A's level checks
# against a function kept, and reached by A's kind (rewrite_id).

def id_name(+a: R.NodeKind) -> String:
  "rw.id." ++ kname(a)

def differs_id(+a: R.NodeKind) -> Bool:
  Bool.not(String.eq(rule_fns(True{}, R.rule_id(a, True{}), "x", a, R.KFn{}), rule_fns(True{}, R.rule_id(a, False{}), "x", a, R.KFn{})))

def id_fns.d(d: Bool, +a: R.NodeKind) -> String:
  match d:
    case True{}:
      rule_fns(True{}, R.rule_id(a, True{}), id_name(a) ++ ".yes", a, R.KFn{}) ++ rule_fns(True{}, R.rule_id(a, False{}), id_name(a) ++ ".no", a, R.KFn{})
    case False{}:
      rule_fns(True{}, R.rule_id(a, False{}), id_name(a), a, R.KFn{})

def id_fns(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      id_fns.d(differs_id(a), a) ++ id_fns(t)

def id_case.d(d: Bool, +a: R.NodeKind) -> String:
  match d:
    case True{}:
      "    case " ++ code(a) ++ ":\n" ++
      "      match t:\n" ++
      "        case True{}:\n" ++
      "          " ++ call(R.rule_id(a, True{}), id_name(a) ++ ".yes", checked(a, R.KFn{})) ++ "\n" ++
      "        case False{}:\n" ++
      "          " ++ call(R.rule_id(a, False{}), id_name(a) ++ ".no", checked(a, R.KFn{})) ++ "\n"
    case False{}:
      "    case " ++ code(a) ++ ":\n" ++
      "      " ++ call(R.rule_id(a, False{}), id_name(a), checked(a, R.KFn{})) ++ "\n"

def id_cases(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      id_case.d(differs_id(a), a) ++ id_cases(t)

def rewrite_id() -> String:
  "# A, negative principal, of kind ka, meeting the identity, its loop\n" ++
  "# resolved ahead (R.rule_id); t is the payload test; a stuck pair counted\n" ++
  "# an error as the rule table's are\n" ++
  "def rewrite_id(" ++ arm_params() ++ ") -> R:\n  match ka:\n" ++ id_cases(kinds()) ++
  "    case _:\n      fin(P.err_if(U32.is_ne(ka, 8), h), st)\n\n"

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
  "# may a collection reduce A, negative principal, meeting B? Never stuck,\n" ++
  "# no more nodes made than freed, no builtin applied, no need for a lazy\n" ++
  "# value touched (heap-strategies.cascade.nongrow), fewer ports left than\n" ++
  "# taken (heap-strategies.erasure.load.cycle.shrink). By the pair's rule,\n" ++
  "# a table: 0 never, 1 always, 2 when the levels agree, 3 when they do\n" ++
  "# not\n" ++
  "def collect_of(+r: U32) -> U32:\n  match r:\n    case 0:\n      0\n" ++ collect_cases(numbered(), 1n) ++ "    case _:\n      0\n\n" ++
  "def collects.k(+k: U32, +ha: U32, +hb: U32) -> Bool:\n  match k:\n    case 1:\n      True{}\n    case 2:\n      P.same_lvl(ha, hb)\n" ++
  "    case 3:\n      Bool.not(P.same_lvl(ha, hb))\n    case _:\n      False{}\n\n" ++
  "def collects(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:\n  collects.k(collect_of(rule_no(ka, kb)), ha, hb)\n\n" ++
  over_a(kinds(), True{}) ++
  id_fns(kinds()) ++
  events() ++
  rewrites() ++
  rewrite_id()

def main() -> IO(Unit):
  IO.print(file())
