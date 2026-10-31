import Base
import ./val.bend as V
import ./rules.bend as R
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X
import ./kprim.bend as P
import ./krules.bend as KR
import ./kmem_grow.bend as KM

# A net in the kernel's node layout (spike-node-layout in
# docs/plans/EvalSpike_2026-10-26.md), over kprim.bend's primitives: how a
# pair is rewritten, how a template is loaded and a result read off the
# interface, and the table's audit. Which pair to rewrite next is a
# strategy's business (kstrat.bend, heap-strategies in
# docs/plans/HeapModel_2026-10-27.md): the net records no pairs, and a
# rewrite comes in two families, the plain one and the eager one, which
# notes the pairs it makes on a strategy's stack (heap-strategies.stack).
#
# Its rewrites are krules.bend's, generated from the rule table (R.rule);
# its reference is the table itself, interpreted here as net.bend does on
# the kernel's layout, which also takes every redex whose external peers
# include its own ports (the identity function's body is its argument):
# those are joined through the rule's links, as net.bend's link_pairs does.
# Payloads of data nodes and calls are linear, as in the generator: the
# first new node using one takes it over, a later one gets a duplicate, a
# rule using it nowhere drops it. Both paths make net.bend's level checks
# (but the sites of two fans meeting at one level) and fuse controls after
# each rewrite as it does, on the same links in the same order.

# Payloads
# ========

# a kind whose payload is a value: data, and a call's or a dead call's
# function
def is_data(+k: U32) -> Bool:
  U32.is_eq(k, 5) || U32.is_eq(k, 9) || U32.is_eq(k, 16)

type Mk is Type:
  Mk{h: P.H, refs: List<&2, U32>, +ua: Bool, +ub: Bool}

def pw.dup(r: P.H & U32, +m: U32, +f: U32) -> P.H & P.PW:
  (h, +w) = r
  (h, P.PW{m, f, w})

# a payload's next use: the first takes it over; a later one, of a data
# node's or a call's, a duplicate
def pay.use(+dup: Bool, h: P.H, +hx: U32, +px: U32) -> P.H & P.PW:
  match dup:
    case True{}:
      pw.dup(P.dup(h, P.form(hx), px), P.form(hx), P.fld(hx))
    case False{}:
      (h, P.PW{P.form(hx), P.fld(hx), px})

# a new node's form, field and payload word, after the rule's source: A's
# and B's headers and payload words, and whether each payload is taken yet
def pay(s: R.Src, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +ua: Bool, +ub: Bool) -> P.H & P.PW:
  match s:
    case R.SNone{}:
      (h, P.PW{0, 0, 0})
    case R.SPayA{}:
      pay.use(ua && is_data(P.rk(ha)), h, ha, pa)
    case R.SPayB{}:
      pay.use(ub && is_data(P.rk(hb)), h, hb, pb)
    case R.SFanA{}:
      (h, P.PW{0, P.fld(ha), 0})
    case R.SFanB{}:
      (h, P.PW{0, P.fld(hb), 0})
    case R.SApply{}:
      P.apply(h, ha, pa, hb, pb)
    case R.SLiftA{}:
      (h, P.PW{0, P.lift(P.fld(hb), pb, P.fld(ha)), pa})
    case R.SLiftB{}:
      (h, P.PW{0, P.lift(P.fld(ha), pa, P.fld(hb)), pb})
    # no rule makes a composed source (law rules_base_sources)
    case R.SAp{f, x}:
      (h, P.PW{0, 0, 0})
    case R.SLft{x, c}:
      (h, P.PW{0, 0, 0})
    case R.SSeg{c, i, j}:
      (h, P.PW{0, 0, 0})

def takes_a(s: R.Src) -> Bool:
  match s:
    case R.SPayA{}:
      True{}
    case R.SApply{}:
      True{}
    case _:
      False{}

def takes_b(s: R.Src) -> Bool:
  match s:
    case R.SPayB{}:
      True{}
    case R.SApply{}:
      True{}
    case _:
      False{}

# Applying a rule
# ===============

def mk.add(r: P.H & U32, refs: List<&2, U32>, +ua: Bool, +ub: Bool) -> Mk:
  (h, +n) = r
  Mk{h, List.append(&2, U32, refs, [n]), ua, ub}

def mk.node(r: P.H & P.PW, +k: R.NodeKind, refs: List<&2, U32>, +ua: Bool, +ub: Bool) -> Mk:
  (h, pw) = r
  mk.add(P.node_pw(h, N.kcode(k), pw), refs, ua, ub)

def mk.step(m: Mk, sp: R.Spec, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Mk:
  match m:
    case Mk{h, refs, +ua, +ub}:
      match sp:
        case R.Spec{+k, +s}:
          mk.node(pay(s, h, ha, hb, pa, pb, ua, ub), k, refs, ua || takes_a(s), ub || takes_b(s))

# allocate the rule's new nodes, in order
def make(xs: List<&2, R.Spec>, +ha: U32, +hb: U32, +pa: U32, +pb: U32, m: Mk) -> Mk:
  match xs:
    case Nil{}:
      m
    case Con{sp, t}:
      make(t, ha, hb, pa, pb, mk.step(m, sp, ha, hb, pa, pb))

def drop_if(d: Bool, h: P.H, +hx: U32, +px: U32) -> P.H:
  match d:
    case True{}:
      P.drop(h, P.form(hx), px)
    case False{}:
      h

# a data payload no new node took, dropped
def drop_unused(m: Mk, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Mk:
  match m:
    case Mk{h, refs, +ua, +ub}:
      Mk{drop_if(is_data(P.rk(hb)) && Bool.not(ub), drop_if(is_data(P.rk(ha)) && Bool.not(ua), h, ha, pa), hb, pb), refs, ua, ub}

def new_ref(+n: U32, +p: Nat, +k: R.NodeKind) -> U32:
  (n + U32.from_nat(p) : U32)

def resolve(+x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, e: R.End) -> U32:
  match e:
    case R.Ext{i}:
      N.ext_at(x, i)
    case R.New{+j, +p}:
      new_ref(N.nth(refs, j), p, R.spec_kind(xs, j))

def internal(+x: N.Ext, +a: U32, +b: U32, e: R.End) -> Bool:
  match e:
    case R.Ext{i}:
      Maybe.is_some(&2, Nat, N.partner(N.ext_at(x, i), a, b))
    case R.New{j, p}:
      False{}

def link_if(b: Bool, h: P.H, +u: U32, +v: U32) -> P.H:
  match b:
    case True{}:
      P.link(h, u, v)
    case False{}:
      h

# link every rule link whose ends are both outside the redex
def link_plain(ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{R.Link{+u, +v}, t}:
      link_plain(t, x, refs, xs, a, b,
        link_if(Bool.not(internal(x, a, b, u) || internal(x, a, b, v)), h, resolve(x, refs, xs, u), resolve(x, refs, xs, v)))

# where an end the rule links to the pair's Ext ends is itself inside, the
# rule's links and the pair's own run round a closed loop of wire, which
# holds nothing and vanishes (R.contract; law rules_pairs_total says no
# other chain through the pair arises)
def pair_link(bad: Bool, +u: R.End, +v: R.End, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, h: P.H) -> P.H:
  match bad:
    case True{}:
      h
    case False{}:
      P.link(h, resolve(x, refs, xs, u), resolve(x, refs, xs, v))

def pair_ends(oi: Maybe<&2, R.End>, oj: Maybe<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match oi oj:
    case Some{+u} Some{+v}:
      pair_link(internal(x, a, b, u) || internal(x, a, b, v), u, v, x, refs, xs, h)
    case _ _:
      P.h_err(h)

def pair_go(lt: Bool, +i: Nat, +j: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match lt:
    case True{}:
      pair_ends(N.other(ls, i), N.other(ls, j), x, refs, xs, a, b, h)
    case False{}:
      h

def pair_at(pt: Maybe<&2, Nat>, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match pt:
    case None{}:
      h
    case Some{+j}:
      pair_go(Nat.is_lt(i, j), i, j, ls, x, refs, xs, a, b, h)

# an external peer that is a port of the redex stands for another
# external: join what the rule links to the two (net.bend's link_pairs)
def link_pairs(n: Nat, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match n:
    case 0n:
      h
    case 1n+p:
      link_pairs(p, 1n+i, ls, x, refs, xs, a, b, pair_at(N.partner(N.ext_at(x, i), a, b), i, ls, x, refs, xs, a, b, h))

# fusion at each link the rule made that may join two controls, as the
# generated rewrites try it
def fuse_ends(es: List<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, h: P.H) -> P.H:
  match es:
    case Nil{}:
      h
    case Con{e, t}:
      fuse_ends(t, x, refs, xs, P.fuse(h, resolve(x, refs, xs, e)))

def fuse_ext.go(skip: Bool, +e: U32, h: P.H) -> P.H:
  match skip:
    case True{}:
      h
    case False{}:
      P.fuse(h, e)

def fuse_ext(+e: U32, +a: U32, +b: U32, h: P.H) -> P.H:
  fuse_ext.go(U32.is_eq(e, P.nil()) || Maybe.is_some(&2, Nat, N.partner(e, a, b)), e, h)

# fusion at each external peer outside the redex: where the redex's own
# ports were joined through it, the links it made are not the rule's
def fuse_exts(+x: N.Ext, +a: U32, +b: U32, h: P.H) -> P.H:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      fuse_ext(e3, a, b, fuse_ext(e2, a, b, fuse_ext(e1, a, b, fuse_ext(e0, a, b, h))))

def fuse_made(partners: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match partners:
    case True{}:
      fuse_exts(x, a, b, h)
    case False{}:
      fuse_ends(N.fuse_ends(xs, ls), x, refs, xs, h)

# The links the interpreter makes between two principal ports, in the
# order link_plain and link_pairs make them: an eager strategy notes
# them, as the generated eager rewrites do (heap-strategies.stack)

def note_of.go(both: Bool, +u: U32) -> List<&2, U32>:
  match both:
    case True{}:
      [u]
    case False{}:
      []

def note_of(+u: U32, +v: U32) -> List<&2, U32>:
  note_of.go(U32.is_eq(P.port(u), 0) && U32.is_eq(P.port(v), 0), u)

def notes_if(c: Bool, +u: U32, +v: U32) -> List<&2, U32>:
  match c:
    case True{}:
      note_of(u, v)
    case False{}:
      []

def notes_plain(ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32) -> List<&2, U32>:
  match ls:
    case Nil{}:
      []
    case Con{R.Link{+u, +v}, t}:
      List.append(&2, U32, notes_if(Bool.not(internal(x, a, b, u) || internal(x, a, b, v)), resolve(x, refs, xs, u), resolve(x, refs, xs, v)),
        notes_plain(t, x, refs, xs, a, b))

def notes_ends(oi: Maybe<&2, R.End>, oj: Maybe<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32) -> List<&2, U32>:
  match oi oj:
    case Some{+u} Some{+v}:
      notes_if(Bool.not(internal(x, a, b, u) || internal(x, a, b, v)), resolve(x, refs, xs, u), resolve(x, refs, xs, v))
    case _ _:
      []

def notes_go(lt: Bool, +i: Nat, +j: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32) -> List<&2, U32>:
  match lt:
    case True{}:
      notes_ends(N.other(ls, i), N.other(ls, j), x, refs, xs, a, b)
    case False{}:
      []

def notes_at(pt: Maybe<&2, Nat>, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32) -> List<&2, U32>:
  match pt:
    case None{}:
      []
    case Some{+j}:
      notes_go(Nat.is_lt(i, j), i, j, ls, x, refs, xs, a, b)

def notes_pairs(n: Nat, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      List.append(&2, U32, notes_at(N.partner(N.ext_at(x, i), a, b), i, ls, x, refs, xs, a, b), notes_pairs(p, 1n+i, ls, x, refs, xs, a, b))

# a rewrite by the table: the net, and the pairs its links made
type Wd is Type:
  Wd{h: P.H, ns: List<&2, U32>}

def wire.made(m: Mk, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext, +a: U32, +b: U32) -> Wd:
  match m:
    case Mk{h, +refs, +ua, +ub}:
      Wd{fuse_made(N.any_partner(x, a, b), xs, ls, x, refs, a, b,
          link_pairs(4n, 0n, ls, x, refs, xs, a, b, link_plain(ls, x, refs, xs, a, b, h))),
        List.append(&2, U32, notes_plain(ls, x, refs, xs, a, b), notes_pairs(4n, 0n, ls, x, refs, xs, a, b))}

# replace the redex a >< b by the rule's nodes and links
def wire(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext) -> Wd:
  wire.made(drop_unused(make(xs, ha, hb, pa, pb, Mk{P.fresh2(h, a, b), Nil{}, False{}, False{}}), ha, hb, pa, pb), xs, ls, x, a, b)

def apply_rule(r: R.Rule, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Wd:
  match r:
    case R.RWire{xs, ls}:
      wire(h, a, b, ha, hb, pa, pb, xs, ls, x)
    case R.RStuck{}:
      Wd{P.err_if(U32.is_ne(P.rk(ha), 8), h), []}

def wd.h(w: Wd) -> P.H:
  match w:
    case Wd{h, ns}:
      h

def push_all(ns: List<&2, U32>, st: P.Stk) -> P.Stk:
  match ns:
    case Nil{}:
      st
    case Con{+x, t}:
      push_all(t, P.push(st, x))

def wd.e(w: Wd, st: P.Stk) -> P.E:
  match w:
    case Wd{h, ns}:
      P.E{h, push_all(ns, st)}

# Interaction
# ===========

def kof(+h: U32) -> R.NodeKind:
  N.kof(P.rk(h))

# ports, by rule kind (generated from R.arity)
def arity(+h: U32) -> U32:
  KR.kind_arity(P.rk(h))

def aux_or_nil(b: Bool, +l: U32) -> U32:
  match b:
    case True{}:
      l
    case False{}:
      P.nil()

def payload.k(+k: U32, +w1: U32, +w3: U32) -> U32:
  match k:
    case 5:
      w1
    case 9:
      w3
    case 10:
      w3
    case 11:
      w3
    case 16:
      w3
    case _:
      0

# a node's payload word: a data node's word 2, a call's, a dead call's or
# a control's 3
def payload(+h: U32, +w1: U32, +w3: U32) -> U32:
  payload.k(P.rk(h), w1, w3)

# is e a port of the redex itself? (net.bend's partner, without the index)
def mine(+e: U32, +a: U32, +b: U32) -> Bool:
  U32.is_ne(e, P.nil()) && (U32.is_eq((e >> 2n : U32), (a >> 2n : U32)) || U32.is_eq((e >> 2n : U32), (b >> 2n : U32)))

def any_partner(+x: N.Ext, +a: U32, +b: U32) -> Bool:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      mine(e0, a, b) || mine(e1, a, b) || mine(e2, a, b) || mine(e3, a, b)

# Events
# ======
#
# heap-strategies.erasure.kernel in docs/plans/HeapModel_2026-10-27.md. In
# the erasure modes, each external peer of a rewrite is looked at after
# it: where an eraser's principal faces an auxiliary port
# its kind erases (KR.ev_by, from R.event), the event runs (KR.event),
# and the node's external peers are looked at in turn. Every link a rule makes
# has an external end but those joining its new nodes, which make no event
# (KR.inner_events), so these are all the events a rewrite makes. An event
# allocates nothing and frees only the eraser, whose principal faces an
# auxiliary port and so is in no active pair; the node keeps its slot and
# its principal's link, its kind changing, and a pair it is in keeps its
# place on a strategy's stack. The ends left to look at wait on a list, so
# that a cascade of any length takes no stack; one may be stale by then, a
# port of a node freed (header 0) or changed meanwhile, and is looked at as
# it now is.
#
# No event frees a node on demand's path, so demand needs no exception:
# the walk reached each node there through an auxiliary port facing the
# principal of the node below, never an eraser's, and an event making its
# node an eraser erased its last auxiliary port (law events_erase_last).
#
# Unlike a rule's, an event's rewrite needs no interpreter where a peer is
# the redex's own: the eraser's one port faces the node, so only the node
# can be its own peer, and polarity allows only a copy's or a merge's
# principal facing its other auxiliary port. Then the rewrite links the
# linear fan's port 1 to its principal, and the link it leaves out, from
# the principal to the port erased, is the one that no longer exists; the
# interpreted table would read the node's ports as a rule's (A's ports 1
# and 2 its external peers 0 and 1), which an event's are not.
#
# The events' state: the net, the family's (a strategy's stack, or
# nothing), the ends left to look at
type Ev<-S: Type> is Type:
  Ev{h: P.H, st: S, ws: List<&2, U32>}

def ws.add.go(none: Bool, +e: U32, ws: List<&2, U32>) -> List<&2, U32>:
  match none:
    case True{}:
      ws
    case False{}:
      Con{e, ws}

def ws.add(+e: U32, ws: List<&2, U32>) -> List<&2, U32>:
  ws.add.go(U32.is_eq(e, P.nil()), e, ws)

def ev.x1.k(one: Bool, +w2: U32, +w3: U32) -> U32:
  match one:
    case True{}:
      w3
    case False{}:
      w2

# the peer of a node's auxiliary port other than p, words 2 and 3 its
# ports' links: none for a node of two ports
def ev.x1(+ha: U32, +p: U32, +w2: U32, +w3: U32) -> U32:
  aux_or_nil(U32.is_eq(arity(ha), 3), ev.x1.k(U32.is_eq(p, 1), w2, w3))

# port n of a node with header hn facing the principal of one with header
# hr, an eraser making an event there
def ev.is(+hn: U32, +n: U32, +hr: U32) -> Bool:
  U32.is_ne(P.port(n), 0) && U32.is_eq(KR.ev_by(P.rk(hn), P.port(n)), P.rk(hr)) && U32.is_ne(P.rk(hr), 0)

def ev.run.fin(~S: Type, r: P.H & S, ws: List<&2, U32>, +k: U32) -> Ev<S>:
  (h, st) = r
  Ev{P.ev_count(h, k), st, ws}

# the event at port p of node a, the eraser b facing it, x0 the peer of
# a's principal and x1 of its other auxiliary port, run and counted, its
# peers to look at; the family's state given room first for the pair the
# event may note
def ev.run(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, h: P.H, st: S, ws: List<&2, U32>, +a: U32, +b: U32, +ha: U32, +hb: U32, +p: U32, +pa: U32, +x0: U32, +x1: U32) -> Ev<S>:
  ev.run.fin(~S, KR.event(~S, ~note, P.rk(ha), p, h, room(st, KR.ev_most()), a, b, ha, hb, pa, 0, x0, x1, P.nil(), P.nil()), ws.add(x0, ws.add(x1, ws)), P.rk(ha))

def ev.w3(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +a: U32, +b: U32, +ha: U32, +hb: U32, +p: U32, +x0: U32, +w2: U32) -> Ev<S>:
  (h, +w3) = r
  ev.run(~S, ~note, ~room, h, st, ws, a, b, ha, hb, p, payload(ha, 0, w3), x0, ev.x1(ha, p, w2, w3))

def ev.w3.r(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +a: U32, +b: U32, +ha: U32, +hb: U32, +p: U32, +x0: U32) -> Ev<S>:
  (h, +w2) = r
  ev.w3(~S, ~note, ~room, P.rd(h, (a + 3 : U32)), st, ws, a, b, ha, hb, p, x0, w2)

def ev.w2(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +a: U32, +b: U32, +ha: U32, +hb: U32, +p: U32) -> Ev<S>:
  (h, +x0) = r
  ev.w3.r(~S, ~note, ~room, P.rd(h, (a + 2 : U32)), st, ws, a, b, ha, hb, p, x0)

# node a's port p facing eraser b's principal, if ok: its words read
def ev.at(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, ok: Bool, h: P.H, st: S, ws: List<&2, U32>, +a: U32, +b: U32, +ha: U32, +hb: U32, +p: U32) -> Ev<S>:
  match ok:
    case True{}:
      ev.w2(~S, ~note, ~room, P.rd(h, (a + 1 : U32)), st, ws, a, b, ha, hb, p)
    case False{}:
      Ev{h, st, ws}

# end e, header hx, and its peer y, header hy: which is the node, which
# the eraser
def ev.ori(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, eprin: Bool, h: P.H, st: S, ws: List<&2, U32>, +e: U32, +y: U32, +hx: U32, +hy: U32) -> Ev<S>:
  match eprin:
    case True{}:
      ev.at(~S, ~note, ~room, ev.is(hy, y, hx), h, st, ws, P.base(y), P.base(e), hy, hx, P.port(y))
    case False{}:
      ev.at(~S, ~note, ~room, ev.is(hx, e, hy) && U32.is_eq(P.port(y), 0), h, st, ws, P.base(e), P.base(y), hx, hy, P.port(e))

def ev.hy(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +e: U32, +y: U32, +hx: U32) -> Ev<S>:
  (h, +hy) = r
  ev.ori(~S, ~note, ~room, U32.is_eq(P.port(e), 0), h, st, ws, e, y, hx, hy)

def ev.y(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +e: U32, +hx: U32) -> Ev<S>:
  (h, +y) = r
  ev.hy(~S, ~note, ~room, P.rd(h, P.base(y)), st, ws, e, y, hx)

def ev.c(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, c: Bool, h: P.H, st: S, ws: List<&2, U32>, +e: U32, +hx: U32) -> Ev<S>:
  match c:
    case True{}:
      ev.y(~S, ~note, ~room, P.rd(h, (e + 1 : U32)), st, ws, e, hx)
    case False{}:
      Ev{h, st, ws}

def ev.hx(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, r: P.H & U32, st: S, ws: List<&2, U32>, +e: U32) -> Ev<S>:
  (h, +hx) = r
  ev.c(~S, ~note, ~room, KR.ev_end(P.rk(hx), P.port(e)), h, st, ws, e, hx)

# end e looked at: only a port that may be one end of an event (KR.ev_end)
# has its peer read
def ev.end(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, h: P.H, st: S, ws: List<&2, U32>, +e: U32) -> Ev<S>:
  ev.hx(~S, ~note, ~room, P.rd(h, P.base(e)), st, ws, e)

def ev.one.go(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, none: Bool, w: Ev<S>, +e: U32) -> Ev<S>:
  match none:
    case True{}:
      w
    case False{}:
      match w:
        case Ev{h, st, ws}:
          ev.end(~S, ~note, ~room, h, st, ws, e)

def ev.one(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~room: S -> @+n:U32 -> S, w: Ev<S>, +e: U32) -> Ev<S>:
  ev.one.go(~S, ~note, ~room, U32.is_eq(e, P.nil()), w, e)

# Families
# --------
#
# spike-templates: what a strategy threads beside the net, the chains
# below generic over it, a copy compiled for each family. The eager
# strategies' (e): a stack, each link a rewrite makes between two
# principal ports noted on it, room made on it before an event; the rest,
# demand's among them: nothing. A template cannot recurse, nor close a
# recursion through its argument (docs/BendIssues.md, "Recursion through
# templates"), so each loop below, the events' drain, is one per family,
# its body the generic step.

def note.u(u: Unit, +x: U32, +y: U32) -> Unit:
  u

def room.u(u: Unit, +n: U32) -> Unit:
  u

def fin.h(h: P.H, u: Unit) -> P.H:
  h

def fin.e(h: P.H, st: P.Stk) -> P.E:
  P.E{h, st}

def wd.u(w: Wd, u: Unit) -> P.H:
  wd.h(w)

# the ends left looked at, until none
def ev.drain(k: Nat, w: Ev<Unit>) -> P.H:
  match k:
    case 0n:
      match w:
        case Ev{h, st, ws}:
          h
    case 1n+f:
      match w:
        case Ev{h, st, ws}:
          match ws:
            case Nil{}:
              h
            case Con{+e, t}:
              ev.drain(f, ev.end(~Unit, ~note.u, ~room.u, h, st, t, e))

# a rewrite's external peers looked at
def ev.settle(h: P.H, +x: N.Ext) -> P.H:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      ev.drain(4294967295n, ev.one(~Unit, ~note.u, ~room.u, ev.one(~Unit, ~note.u, ~room.u, ev.one(~Unit, ~note.u, ~room.u,
        ev.one(~Unit, ~note.u, ~room.u, Ev{h, Unit{}, Nil{}}, e0), e1), e2), e3))

def ev.drain.e(k: Nat, w: Ev<P.Stk>) -> P.E:
  match k:
    case 0n:
      match w:
        case Ev{h, st, ws}:
          P.E{h, st}
    case 1n+f:
      match w:
        case Ev{h, st, ws}:
          match ws:
            case Nil{}:
              P.E{h, st}
            case Con{+e, t}:
              ev.drain.e(f, ev.end(~P.Stk, ~P.note, ~P.room, h, st, t, e))

def ev.settle.e(r: P.E, +x: N.Ext) -> P.E:
  match r:
    case P.E{h, st}:
      match x:
        case N.Ext4{+e0, +e1, +e2, +e3}:
          ev.drain.e(4294967295n, ev.one(~P.Stk, ~P.note, ~P.room, ev.one(~P.Stk, ~P.note, ~P.room, ev.one(~P.Stk, ~P.note, ~P.room,
            ev.one(~P.Stk, ~P.note, ~P.room, Ev{h, st, Nil{}}, e0), e1), e2), e3))

# what follows a rewrite: nothing, or (ev.settle) the events it makes
def go.none(h: P.H, +x: N.Ext) -> P.H:
  h

def go.none.e(r: P.E, +x: N.Ext) -> P.E:
  r

# The chain
# ---------
#
# A rewrite of an active pair, generic over the family: S and its `note`,
# R and `fin` its result, `wd` the interpreted table's, and `after`, what
# follows each rewrite. From `interact` down through the generated
# rewrites every function is a template, each strategy compiling a chain
# of its own, every function beneath called from one copy only, which Bend
# folds (heap-strategies.erasure.kernel.parity).

# the generated rewrite, which calls `after` itself at the external peers
# where its rule may make an event (gen_krules.bend's sites)
def go.gen(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, +rn: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> R:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite(~S, ~R, ~note, ~fin, ~after, P.rk(ha), rn, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def go.interp.pl(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.Pl, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> R:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      after(wd(apply_rule(R.rule(kof(ha), kof(hb), t), h, a, b, ha, hb, pa, pb, N.Ext4{e0, e1, e2, e3}), st), N.Ext4{e0, e1, e2, e3})

# the interpreted table, then `after` at all its external peers; a Lift
# facing a LiftC is peeled first, as the generated rewrite for the pair
# does (kprim.bend's peel_ctl), the peers then those peeling leaves
def go.interp(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, ctl: Bool, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> R:
  match ctl:
    case True{}:
      match x:
        case N.Ext4{+e0, +e1, +e2, +e3}:
          go.interp.pl(~S, ~R, ~note, ~fin, ~wd, ~after, P.peel_ctl(KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case False{}:
      after(wd(apply_rule(R.rule(kof(ha), kof(hb), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, x), st), x)

def go.which(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, gen: Bool, +rn: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> R:
  match gen:
    case True{}:
      go.gen(~S, ~R, ~note, ~fin, ~wd, ~after, rn, t, h, st, a, b, ha, hb, pa, pb, x)
    case False{}:
      go.interp(~S, ~R, ~note, ~fin, ~wd, ~after, U32.is_eq(P.rk(ha), 10) && U32.is_eq(P.rk(hb), 11), t, h, st, a, b, ha, hb, pa, pb, x)

# the generated rewrite, or the interpreted table: for a redex whose
# external peers include its own ports, or when `fast` is off
def go.rule(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & Bool, st: S, +fast: Bool, +rn: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> R:
  (h, +t) = r
  go.which(~S, ~R, ~note, ~fin, ~wd, ~after, fast && Bool.not(any_partner(x, a, b)), rn, t, h, st, a, b, ha, hb, pa, pb, x)

# the pair's rule by number (KR.rule_no), read once for the payload test
# and the rewrite
def go.ext.r(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, +rn: U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: S) -> R:
  go.rule(~S, ~R, ~note, ~fin, ~wd, ~after, KR.test(~S, ~R, ~note, ~fin, ~after, rn, h, ha, hb, payload(ha, 0, a2), payload(hb, b1, b2)), st, fast, rn, a, b, ha, hb, payload(ha, 0, a2), payload(hb, b1, b2),
    N.Ext4{aux_or_nil(U32.is_lt(1, arity(ha)), a1), aux_or_nil(U32.is_lt(2, arity(ha)), a2),
      aux_or_nil(U32.is_lt(1, arity(hb)), b1), aux_or_nil(U32.is_lt(2, arity(hb)), b2)})

def go.ext(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: S) -> R:
  go.ext.r(~S, ~R, ~note, ~fin, ~wd, ~after, KR.rule_no(P.rk(ha), P.rk(hb)), fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

def go.b2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32) -> R:
  (h, +b2) = r
  go.ext(~S, ~R, ~note, ~fin, ~wd, ~after, fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

def go.b1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32) -> R:
  (h, +b1) = r
  go.b2(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, (b + 3 : U32)), st, fast, a, b, ha, hb, a1, a2, b1)

def go.a2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32) -> R:
  (h, +a2) = r
  go.b1(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, (b + 2 : U32)), st, fast, a, b, ha, hb, a1, a2)

def go.a1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> R:
  (h, +a1) = r
  go.a2(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, (a + 3 : U32)), st, fast, a, b, ha, hb, a1)

# a's principal is negative. Words 2 and 3 are ports 1 and 2's links, or
# a node's payload: a data node's word 2, a call's or a control's word 3.
def go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> R:
  go.a1(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, (a + 2 : U32)), st, fast, a, b, ha, hb)

def ori(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, neg: Bool, h: P.H, st: S, +fast: Bool, +x: U32, +y: U32, +hx: U32, +hy: U32) -> R:
  match neg:
    case True{}:
      go(~S, ~R, ~note, ~fin, ~wd, ~after, h, st, fast, x, y, hx, hy)
    case False{}:
      go(~S, ~R, ~note, ~fin, ~wd, ~after, h, st, fast, y, x, hy, hx)

def int.y(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +x: U32, +y: U32, +hx: U32) -> R:
  (h, +hy) = r
  ori(~S, ~R, ~note, ~fin, ~wd, ~after, KR.kind_neg(P.rk(hx)), h, st, fast, x, y, hx, hy)

def int.x(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +fast: Bool, +x: U32, +y: U32) -> R:
  (h, +hx) = r
  int.y(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, y), st, fast, x, y, hx)

# rewrite the active pair x >< y
def interact.f(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~wd: Wd -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +fast: Bool, +x: U32, +y: U32) -> R:
  int.x(~S, ~R, ~note, ~fin, ~wd, ~after, P.rd(h, x), st, fast, x, y)

# The families' chains: the net alone, and with a strategy's stack, on
# which each rewrite notes the pairs it makes, in the order it makes them
# (heap-strategies.stack). Demand's walk calls `go` itself, with the plain
# family's arguments: a wrapper there, called from two places, would stay
# a function of its own, a call more for every rewrite on demand (1.3% to
# 2.4% of its instructions, store run 84).

def interact(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +fast: Bool, +x: U32, +y: U32) -> P.H:
  interact.f(~Unit, ~P.H, ~note.u, ~fin.h, ~wd.u, ~after, h, Unit{}, fast, x, y)

def interact.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +fast: Bool, +x: U32, +y: U32) -> P.E:
  interact.f(~P.Stk, ~P.E, ~P.note, ~fin.e, ~wd.e, ~after, h, st, fast, x, y)

# Loading a template
# ==================

def lift_word(+up: Bool, +by: U32) -> U32:
  match up:
    case True{}:
      (by .|. 2147483648 : U32)
    case False{}:
      by

def drop_ref(r: P.H & U32) -> P.H:
  (h, +n) = r
  h

def load.data(r: P.H & P.PW, +k: U32) -> P.H:
  (h, pw) = r
  drop_ref(P.node_pw(h, k, pw))

def fan_hd.go(none: Bool, +k: U32, +site: U32, +lvl: U32) -> U32:
  match none:
    case True{}:
      P.hd2(k, P.unlev(), site)
    case False{}:
      P.hd(k, lvl)

# a fan's header: its level, or for a net built without levels its site,
# marked so
def fan_hd(+k: U32, +site: U32, +lvl: U32) -> U32:
  fan_hd.go(U32.is_eq(lvl, V.nolvl()), k, site, lvl)

# a node with no payload: a function or an application without a level
# marked so
def bare_hd(+k: U32) -> U32:
  match k:
    case 1:
      P.hd2(k, P.unlev(), 0)
    case 2:
      P.hd2(k, P.unlev(), 0)
    case _:
      P.hd(k, 0)

def too_big(+f: U32) -> Bool:
  U32.is_ge(f, P.lvl_cap())

# the field a fan keeps, its site without a level, else its level
def fan_too_big(none: Bool, +site: U32, +lvl: U32) -> Bool:
  match none:
    case True{}:
      too_big(site)
    case False{}:
      too_big(lvl)

# a node from its template; a level, site or index past the field's 22
# bits, or an offset past 31, would be cut short: an error
def load.node(h: P.H, t: T.TNode) -> P.H:
  match t:
    case T.TF{k, +site, +lvl}:
      P.err_if(fan_too_big(U32.is_eq(lvl, V.nolvl()), site, lvl),
        drop_ref(P.node(h, fan_hd(N.kcode(k), site, lvl), 0)))
    case T.TN{k, p}:
      match p:
        case V.PVal{v}:
          load.data(P.put(h, v), N.kcode(k))
        case V.PLvl{+l}:
          P.err_if(too_big(l), drop_ref(P.node(h, P.hd(N.kcode(k), l), 0)))
        case V.PLift{+n, +up, +by}:
          P.err_if(too_big(n) || U32.is_ge(by, 2147483648),
            drop_ref(P.node(h, P.hd(N.kcode(k), n), lift_word(up, by))))
        case _:
          drop_ref(P.node(h, bare_hd(N.kcode(k)), 0))

def load.nodes(ns: List<&2, T.TNode>, h: P.H) -> P.H:
  match ns:
    case Nil{}:
      h
    case Con{t, rest}:
      load.nodes(rest, load.node(h, t))

# a template's node n is the net's node n + 4, after the header and the
# interface (kprim.bend's first)
def tref(e: T.TEnd) -> U32:
  match e:
    case T.TE{+n, +p}:
      (((n + (P.first() + 1 : U32) : U32) << 2n : U32) + p : U32)

def load.links(ls: List<&2, T.TLink>, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{T.TL{x, y}, rest}:
      load.links(rest, P.link(h, tref(x), tref(y)))

def load.root(r: P.H & U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +x: U32) -> P.H:
  (h, +root) = r
  P.link(load.links(links, load.nodes(nodes, h)), root, x)

# the template's net, its exposed port linked to the interface: node 3,
# the first after the header, which keeps its slot for good (HeapModel's
# "Nets")
def load(t: T.Tpl) -> P.H:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      load.root(P.node(P.h_new(), P.hd(8, 0), 0), nodes, links, tref(root))

# Results
# =======

# the value read off the root, as glam sees it (V.norm)
def value.v(r: P.H & V.Val) -> P.H & Maybe<&2, V.Val>:
  (h, v) = r
  (h, Some{V.norm(v)})

def value.w(r: P.H & U32, +hp: U32) -> P.H & Maybe<&2, V.Val>:
  (h, +w) = r
  value.v(P.peek(h, P.form(hp), P.fld(hp), w))

def value.is(data: Bool, h: P.H, +hp: U32, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  match data:
    case True{}:
      value.w(P.rd(h, (pn + 2 : U32)), hp)
    case False{}:
      (h, None{})

def value.h(r: P.H & U32, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  (h, +hp) = r
  value.is(U32.is_eq(P.rk(hp), 5), h, hp, pn)

def value.peer(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +peer) = r
  value.h(P.rd(h, P.base(peer)), P.base(peer))

def value.none(none: Bool, h: P.H, +root: U32) -> P.H & Maybe<&2, V.Val>:
  match none:
    case True{}:
      (h, None{})
    case False{}:
      value.peer(P.rd(h, (root + 1 : U32)))

def value.root(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +hdr) = r
  value.none(U32.is_ne(P.kind(hdr), 8), h, P.iface())

# the value at the interface: its peer's, when that is data
def result(h: P.H) -> P.H & Maybe<&2, V.Val>:
  value.root(P.rd(h, P.iface()))

def counts.st(r: P.H & P.HS) -> String:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++ U32.show(cap) ++ " nodes capacity, " ++
        U32.show(P.h_live(h)) ++ " data entries live"

def counts(h: P.H) -> String:
  counts.st(P.stats(h))

def show_val(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "a non-number"
    case None{}:
      "no value"

def table_str(+ok: Bool) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      ", TABLE MISMATCH"

def need_str(+need: Bool, +lz: U32) -> String:
  match need:
    case True{}:
      " cell " ++ U32.show(lz)
    case False{}:
      ""

def report(r: P.H & Maybe<&2, V.Val>) -> String:
  (h, v) = r
  show_val(v) ++ ", " ++ counts(h)

# Auditing the table
# ==================

# live nodes holding a table entry (data nodes and calls of form 0),
# which a linear table matches with its live entries one for one
type Au is Type:
  Au{h: P.H, +n: U32}

def audit.one(+tab: Bool, +n: U32) -> U32:
  match tab:
    case True{}:
      (n + 1 : U32)
    case False{}:
      n

def audit.hit(r: P.H & U32, +n: U32) -> Au:
  (h, +hdr) = r
  Au{h, audit.one(is_data(P.rk(hdr)) && U32.is_eq(P.form(hdr), 0) && U32.is_ne(hdr, 0), n)}

def audit(k: Nat, +i: U32, au: Au) -> Au:
  match k:
    case 0n:
      au
    case 1n+p:
      match au:
        case Au{h, +n}:
          audit(p, (i + 1 : U32), audit.hit(P.rd(h, (i << 2n : U32)), n))

# The free list's audit: a node is free exactly when its header is 0
# (kprim.bend's free), so the list from its head must hold only nodes past
# the header and within the capacity, each with a zero header, end within
# as many steps as there are nodes (else it runs round a cycle), and hold
# as many nodes as have a zero header.
type Fl is Type:
  Fl{h: P.H, +j: U32, +n: U32, +ok: Bool}

def fl.nx(r: P.H & U32, +n: U32, +ok: Bool) -> Fl:
  (h, +nx) = r
  Fl{h, nx, n, ok}

def fl.hd(r: P.H & U32, +i: U32, +n: U32, +ok: Bool) -> Fl:
  (h, +hd) = r
  fl.nx(P.rd(h, ((i << 2n : U32) + 1 : U32)), (n + 1 : U32), ok && U32.is_eq(hd, 0))

# node i, the list's next: read if past the header and within the
# capacity, else the walk ends, failed
def fl.at(inside: Bool, h: P.H, +i: U32, +n: U32, +ok: Bool) -> Fl:
  match inside:
    case True{}:
      fl.hd(P.rd(h, (i << 2n : U32)), i, n, ok)
    case False{}:
      Fl{h, 0, n, False{}}

def fl.go(k: Nat, s: Fl, +cap: U32) -> Fl:
  match k:
    case 0n:
      match s:
        case Fl{h, +j, +n, +ok}:
          Fl{h, j, n, ok && U32.is_eq(j, 0)}
    case 1n+p:
      match s:
        case Fl{h, +j, +n, +ok}:
          match j:
            case 0:
              Fl{h, 0, n, ok}
            case _:
              fl.go(p, fl.at(U32.is_ge((j - 1 : U32), P.first()) && U32.is_lt((j - 1 : U32), cap), h, (j - 1 : U32), n, ok), cap)

def fz.one(r: P.H & U32, +c: U32) -> P.H & U32:
  (h, +hd) = r
  (h, audit.one(U32.is_eq(hd, 0), c))

def fz.step(r: P.H & U32, +i: U32) -> P.H & U32:
  (h, +c) = r
  fz.one(P.rd(h, (i << 2n : U32)), c)

# the nodes from i with a zero header, k of them read
def fz(k: Nat, +i: U32, r: P.H & U32) -> P.H & U32:
  match k:
    case 0n:
      r
    case 1n+p:
      fz(p, (i + 1 : U32), fz.step(r, i))

def fo.cmp(r: P.H & U32, +n: U32, +ok: Bool) -> P.H & Bool:
  (h, +z) = r
  (h, ok && U32.is_eq(z, n))

def fo.fl(s: Fl, +cap: U32) -> P.H & Bool:
  match s:
    case Fl{h, +j, +n, +ok}:
      fo.cmp(fz(U32.to_nat((cap - P.first() : U32)), P.first(), (h, 0)), n, ok)

def fo.fh(r: P.H & U32, +cap: U32) -> P.H & Bool:
  (h, +fh) = r
  fo.fl(fl.go(U32.to_nat(cap), Fl{h, fh, 0, True{}}, cap), cap)

def fo.st(r: P.H & P.HS) -> P.H & Bool:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      fo.fh(P.rd(h, P.at_fh()), cap)

# is the free list in step with the nodes' headers?
def free_ok(h: P.H) -> P.H & Bool:
  fo.st(P.stats(h))

# The wiring's audit (heap-strategies.net.wiring.audit): every port of a
# live node links a port of a live node, past the header and within the
# capacity, below its kind's arity, that links it back, and is not itself.
# So each live port is referenced exactly once and no free node at all, as
# wiring.bend's W.wired says of the model: two ports linking one port
# would both have to be its link.
type Wa is Type:
  Wa{h: P.H, +ok: Bool}

# y's own link, which must be x
def wa.back(r: P.H & U32, +x: U32, +ok: Bool) -> Wa:
  (h, +z) = r
  Wa{h, ok && U32.is_eq(z, x)}

def wa.live(live: Bool, h: P.H, +x: U32, +y: U32, +ok: Bool) -> Wa:
  match live:
    case True{}:
      wa.back(P.rd(h, (y + 1 : U32)), x, ok)
    case False{}:
      Wa{h, False{}}

# y's node's header: live, with y below its arity
def wa.peer(r: P.H & U32, +x: U32, +y: U32, +ok: Bool) -> Wa:
  (h, +hy) = r
  wa.live(U32.is_ne(hy, 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(hy))), h, x, y, ok)

def wa.at(inside: Bool, h: P.H, +x: U32, +y: U32, +ok: Bool) -> Wa:
  match inside:
    case True{}:
      wa.peer(P.rd(h, P.base(y)), x, y, ok)
    case False{}:
      Wa{h, False{}}

# port x's link y: a port of a node past the header and within the
# capacity, not x
def wa.link(r: P.H & U32, +x: U32, +cap: U32, +ok: Bool) -> Wa:
  (h, +y) = r
  wa.at(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), h, x, y, ok)

# node i4 / 4's ports from p, k of them
def wa.ports(k: Nat, +i4: U32, +p: U32, +cap: U32, s: Wa) -> Wa:
  match k:
    case 0n:
      s
    case 1n+q:
      match s:
        case Wa{h, +ok}:
          wa.ports(q, i4, (p + 1 : U32), cap, wa.link(P.rd(h, ((i4 + p : U32) + 1 : U32)), (i4 + p : U32), cap, ok))

# a node's ports, by its kind's arity: none for a free node
def wa.node(r: P.H & U32, +i4: U32, +cap: U32, +ok: Bool) -> Wa:
  (h, +hd) = r
  wa.ports(U32.to_nat(KR.kind_arity(P.rk(hd))), i4, 0, cap, Wa{h, ok})

def wa.go(k: Nat, +i: U32, +cap: U32, s: Wa) -> Wa:
  match k:
    case 0n:
      s
    case 1n+q:
      match s:
        case Wa{h, +ok}:
          wa.go(q, (i + 1 : U32), cap, wa.node(P.rd(h, (i << 2n : U32)), (i << 2n : U32), cap, ok))

def wa.fin(s: Wa) -> P.H & Bool:
  match s:
    case Wa{h, +ok}:
      (h, ok)

def wa.st(r: P.H & P.HS) -> P.H & Bool:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      wa.fin(wa.go(U32.to_nat((cap - P.first() : U32)), P.first(), cap, Wa{h, True{}}))

# is every live port linked to a live port that links it back?
def wired_ok(h: P.H) -> P.H & Bool:
  wa.st(P.stats(h))

# Reachability (heap-strategies.cascade): the nodes a walk along links
# reaches from the interface, each marked once in a bitmap, a word per 32
# nodes, and kept on a worklist until its ports are followed. A live node
# it does not reach is cut off from the interface: garbage no reduction
# can make observable.
type Rc is Type:
  Rc{h: P.H, mk: KM.M, wl: KM.M, +n: U32, +c: U32}

def rc.bit(+j: U32) -> U32:
  (1 << U32.to_nat((j .&. 31 : U32)) : U32)

def rc.push(new: Bool, h: P.H, mk: KM.M, wl: KM.M, +n: U32, +c: U32, +j: U32) -> Rc:
  match new:
    case True{}:
      Rc{h, mk, KM.m_set(wl, n, j), (n + 1 : U32), (c + 1 : U32)}
    case False{}:
      Rc{h, mk, wl, n, c}

def rc.mark(r: KM.M & U32, h: P.H, wl: KM.M, +n: U32, +c: U32, +j: U32) -> Rc:
  (mk, +v) = r
  rc.push(U32.is_eq((v .&. rc.bit(j) : U32), 0), h, KM.m_set(mk, (j >> 5n : U32), (v .|. rc.bit(j) : U32)), wl, n, c, j)

def rc.see.go(ok: Bool, h: P.H, mk: KM.M, wl: KM.M, +n: U32, +c: U32, +j: U32) -> Rc:
  match ok:
    case True{}:
      rc.mark(KM.m_get(mk, (j >> 5n : U32)), h, wl, n, c, j)
    case False{}:
      Rc{h, mk, wl, n, c}

# the node behind reference p, marked and put on the worklist if new
def rc.see(+p: U32, h: P.H, mk: KM.M, wl: KM.M, +n: U32, +c: U32) -> Rc:
  rc.see.go(U32.is_ne(p, P.nil()), h, mk, wl, n, c, (p >> 2n : U32))

def rc.port.r(r: P.H & U32, mk: KM.M, wl: KM.M, +n: U32, +c: U32) -> Rc:
  (h, +q) = r
  rc.see(q, h, mk, wl, n, c)

def rc.port(s: Rc, +i: U32, +p: U32) -> Rc:
  match s:
    case Rc{h, mk, wl, +n, +c}:
      rc.port.r(P.rd(h, (((i << 2n : U32) + 1 : U32) + p : U32)), mk, wl, n, c)

def rc.ports(+a: U32, s: Rc, +i: U32) -> Rc:
  match a:
    case 1:
      rc.port(s, i, 0)
    case 2:
      rc.port(rc.port(s, i, 0), i, 1)
    case _:
      rc.port(rc.port(rc.port(s, i, 0), i, 1), i, 2)

def rc.node(r: P.H & U32, mk: KM.M, wl: KM.M, +n: U32, +c: U32, +i: U32) -> Rc:
  (h, +hd) = r
  rc.ports(KR.kind_arity(P.rk(hd)), Rc{h, mk, wl, n, c}, i)

def rc.pop(r: KM.M & U32, h: P.H, mk: KM.M, +n: U32, +c: U32) -> Rc:
  (wl, +j) = r
  rc.node(P.rd(h, (j << 2n : U32)), mk, wl, n, c, j)

def rc.go(k: Nat, s: Rc) -> Rc:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Rc{h, mk, wl, +n, +c}:
          match n:
            case 0:
              Rc{h, mk, wl, 0, c}
            case _:
              rc.go(p, rc.pop(KM.m_get(wl, (n - 1 : U32)), h, mk, (n - 1 : U32), c))

def rc.fin(s: Rc) -> P.H & U32:
  match s:
    case Rc{h, mk, wl, +n, +c}:
      (h, c)

def rc.wl(r: KM.M & U32, h: P.H, mk: KM.M, +cap: U32) -> P.H & U32:
  (wl, +room) = r
  rc.fin(rc.go(U32.to_nat((cap + 1 : U32)), rc.see(P.iface(), h, mk, wl, 0, 0)))

def rc.ensure(r: KM.M & U32, +words: U32) -> KM.M & U32:
  (m, +cap) = r
  KM.m_ensure(m, words, cap, P.w_maxd())

# a zeroed array of `words` words at least, and its size
def rc.new(+words: U32) -> KM.M & U32:
  rc.ensure(KM.m_new(6n, P.w_maxd()), words)

def rc.mk(r: KM.M & U32, h: P.H, +cap: U32) -> P.H & U32:
  (mk, +room) = r
  rc.wl(rc.new((cap + 1 : U32)), h, mk, cap)

def reach.st(r: P.H & P.HS) -> P.H & U32:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      rc.mk(rc.new(((cap >> 5n : U32) + 1 : U32)), h, cap)

# the nodes reached from the interface along links, the interface's own
# among them
def reach(h: P.H) -> P.H & U32:
  reach.st(P.stats(h))

# Sweeping (heap-strategies.cascade): every live node the walk from the
# interface does not reach freed, a data node's, a call's or a dead
# call's table entry released with it. Nothing reached links to what is freed, so nothing
# dangles; what is freed could never be observed.
type Sw is Type:
  Sw{h: P.H, mk: KM.M, +f: U32}

def sw.pd(r: P.H & U32, +hd: U32) -> P.H:
  (h, +w) = r
  P.drop(h, P.form(hd), w)

def sw.payload(+k: U32, h: P.H, +i: U32, +hd: U32) -> P.H:
  match k:
    case 5:
      sw.pd(P.rd(h, ((i << 2n : U32) + 2 : U32)), hd)
    case 9:
      sw.pd(P.rd(h, ((i << 2n : U32) + 3 : U32)), hd)
    case 16:
      sw.pd(P.rd(h, ((i << 2n : U32) + 3 : U32)), hd)
    case _:
      h

def sw.free(dead: Bool, h: P.H, mk: KM.M, +f: U32, +i: U32, +hd: U32) -> Sw:
  match dead:
    case True{}:
      Sw{P.free(sw.payload(P.rk(hd), h, i, hd), (i << 2n : U32)), mk, (f + 1 : U32)}
    case False{}:
      Sw{h, mk, f}

def sw.m(r: KM.M & U32, h: P.H, +f: U32, +i: U32, +hd: U32) -> Sw:
  (mk, +v) = r
  sw.free(U32.is_ne(hd, 0) && U32.is_eq((v .&. rc.bit(i) : U32), 0), h, mk, f, i, hd)

def sw.hd(r: P.H & U32, mk: KM.M, +f: U32, +i: U32) -> Sw:
  (h, +hd) = r
  sw.m(KM.m_get(mk, (i >> 5n : U32)), h, f, i, hd)

def sw.go(k: Nat, +i: U32, s: Sw) -> Sw:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sw{h, mk, +f}:
          sw.go(p, (i + 1 : U32), sw.hd(P.rd(h, (i << 2n : U32)), mk, f, i))

def sw.fin(s: Sw) -> P.H & U32:
  match s:
    case Sw{h, mk, +f}:
      (h, f)

def sw.start(s: Rc, +cap: U32) -> P.H & U32:
  match s:
    case Rc{h, mk, wl, +n, +c}:
      sw.fin(sw.go(U32.to_nat((cap - P.first() : U32)), P.first(), Sw{h, mk, 0}))

def sweep.wl(r: KM.M & U32, h: P.H, mk: KM.M, +cap: U32) -> P.H & U32:
  (wl, +room) = r
  sw.start(rc.go(U32.to_nat((cap + 1 : U32)), rc.see(P.iface(), h, mk, wl, 0, 0)), cap)

def sweep.mk(r: KM.M & U32, h: P.H, +cap: U32) -> P.H & U32:
  (mk, +room) = r
  sweep.wl(rc.new((cap + 1 : U32)), h, mk, cap)

def sweep.st(r: P.H & P.HS) -> P.H & U32:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      sweep.mk(rc.new(((cap >> 5n : U32) + 1 : U32)), h, cap)

# every node the interface does not reach freed: the net, and the nodes
# freed
def sweep(h: P.H) -> P.H & U32:
  sweep.st(P.stats(h))

