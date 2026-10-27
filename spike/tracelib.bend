import Base
import ./val.bend as V
import ./rules.bend as R
import ./store.bend as S
import ./net.bend as N
import ./tpl.bend as T

# Traced runs of a template net, as text: each interaction as the reducer
# met it, then the result, a census of node kinds, and every live node.
#
# A node is named n<serial>: the template's nodes are n0, n1, ... in
# template order, then each new node takes the next number, so a name is
# never reused. An interaction line: its number, the negative node then
# the positive one (kind, name, payload: a fan's label as site.inst), the
# rule taken, the redex's external peers (A's ports 1, 2, then B's) as
# name.port, and the nodes it made. A node line: name, kind, payload, and
# each port's peer.

def kname.k(+k: U32) -> String:
  match k:
    case 1:
      "Fn"
    case 2:
      "Ap"
    case 3:
      "Copy"
    case 4:
      "Merge"
    case 5:
      "Data"
    case 6:
      "EraN"
    case 7:
      "EraP"
    case 8:
      "Root"
    case 9:
      "Call"
    case _:
      "Free"

def kname(+h: U32) -> String:
  kname.k((h .&. 15 : U32))

def val_str(v: V.Val) -> String:
  match v:
    case V.VNum{+n}:
      U32.show(n)
    case V.VFun{+op, +need, args}:
      match op:
        case 1:
          "succ"
        case 2:
          "add/" ++ U32.show(need)
        case _:
          "fn"
    case _:
      "unit"

def pay_str(p: V.Pay) -> String:
  match p:
    case V.PNone{}:
      ""
    case V.PVal{v}:
      "[" ++ val_str(v) ++ "]"
    case V.PFan{f}:
      match f:
        case V.FanId{+site, +inst}:
          "[" ++ U32.show(site) ++ "." ++ U32.show(inst) ++ "]"

# a node's name, from its header
def hname(+h: U32) -> String:
  "n" ++ U32.show((h >> 4n : U32))

def peer_str.go(nil: Bool, +r: U32, +h: U32) -> String:
  match nil:
    case True{}:
      "-"
    case False{}:
      hname(h) ++ "." ++ U32.show(S.ref_port(r))

# a reference r to a port of the node with header h
def peer_str(+r: U32, +h: U32) -> String:
  peer_str.go(U32.is_eq(r, S.nil()), r, h)

def fans_name(t: Bool) -> String:
  match t:
    case True{}:
      "join"
    case False{}:
      "commute"

def call_name(t: Bool) -> String:
  match t:
    case True{}:
      "call"
    case False{}:
      "stuck"

# the rule's name, after R.rule's cases
def rule_name(ka: R.NodeKind, kb: R.NodeKind, t: Bool) -> String:
  match ka kb:
    case R.KAp{} R.KFn{}:
      "beta"
    case R.KAp{} R.KMerge{}:
      "apply superposition"
    case R.KAp{} R.KData{}:
      call_name(t)
    case R.KAp{} R.KEraP{}:
      "apply error"
    case R.KCopy{} R.KFn{}:
      "copy function"
    case R.KCopy{} R.KMerge{}:
      fans_name(t)
    case R.KCopy{} R.KData{}:
      "copy data"
    case R.KCopy{} R.KEraP{}:
      "copy error"
    case R.KEraN{} _:
      "erase"
    case R.KCall{} R.KData{}:
      "compute"
    case R.KCall{} R.KMerge{}:
      "distribute"
    case R.KCall{} R.KEraP{}:
      "error"
    case R.KRoot{} _:
      "result"
    case _ _:
      "stuck"

def ext_str(+x: N.Ext, +xh: N.Ext) -> String:
  match x xh:
    case N.Ext4{+e0, +e1, +e2, +e3} N.Ext4{+h0, +h1, +h2, +h3}:
      peer_str(e0, h0) ++ " " ++ peer_str(e1, h1) ++ " | " ++ peer_str(e2, h2) ++ " " ++ peer_str(e3, h3)

def made_str.go(none: Bool, +s0: U32, +s1: U32) -> String:
  match none:
    case True{}:
      ""
    case False{}:
      "  made n" ++ U32.show(s0) ++ "-n" ++ U32.show((s1 - 1 : U32))

def made_str(+s0: U32, +s1: U32) -> String:
  made_str.go(U32.is_eq(s0, s1), s0, s1)

def kof(+h: U32) -> R.NodeKind:
  N.kof((h .&. 15 : U32))

def ev_line(ev: N.Ev) -> String:
  match ev:
    case N.Ev{+i, +a, +b, +ha, +hb, +pa, +pb, +x, +xh, +s0, +s1}:
      "#" ++ U32.show(i) ++ "  " ++ kname(ha) ++ " " ++ hname(ha) ++ pay_str(pa) ++ " >< " ++
        kname(hb) ++ " " ++ hname(hb) ++ pay_str(pb) ++ "  " ++
        rule_name(kof(ha), kof(hb), N.rule_test(kof(ha), kof(hb), pa, pb)) ++
        "  ext " ++ ext_str(x, xh) ++ made_str(s0, s1)

def ev_num(ev: N.Ev) -> U32:
  match ev:
    case N.Ev{+i, +a, +b, +ha, +hb, pa, pb, +x, +xh, +s0, +s1}:
      i

def ev_keep(keep: Bool, ev: N.Ev, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      ev_line(ev) <> rest
    case False{}:
      rest

# the lines of the interactions numbered from `from` on, oldest first
def ev_lines(evs: List<&2, N.Ev>, +from: U32) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      ev_keep(U32.is_ge(ev_num(e), from), e, ev_lines(t, from))

# The live nodes
# ==============

type Dm is Type:
  Dm{q: N.Q, ls: List<&2, String>, ks: List<&2, U32>}

def port_strs(n: Nat, +k: Nat, +ls: List<&2, U32>, +hs: List<&2, U32>) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "  " ++ Nat.show(k) ++ ":" ++ peer_str(N.nth(ls, k), N.nth(hs, k)) ++ port_strs(p, 1n+k, ls, hs)

def node_line(+h: U32, +ls: List<&2, U32>, +hs: List<&2, U32>, p: V.Pay) -> String:
  hname(h) ++ " " ++ kname(h) ++ pay_str(p) ++ port_strs(R.arity(kof(h)), 0n, ls, hs)

def dump.fin(r: N.Q & U32, +h: U32, +l0: U32, +l1: U32, +l2: U32, +h0: U32, +h1: U32, p: V.Pay, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +h2) = r
  Dm{q, node_line(h, [l0, l1, l2], [h0, h1, h2], p) <> ls, (h .&. 15 : U32) <> ks}

def dump.h1(r: N.Q & U32, +h: U32, +l0: U32, +l1: U32, +l2: U32, +h0: U32, p: V.Pay, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +h1) = r
  dump.fin(N.ph(q, l2), h, l0, l1, l2, h0, h1, p, ls, ks)

def dump.h0(r: N.Q & U32, +h: U32, +l0: U32, +l1: U32, +l2: U32, p: V.Pay, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +h0) = r
  dump.h1(N.ph(q, l1), h, l0, l1, l2, h0, p, ls, ks)

def dump.pay(r: N.Q & V.Pay, +h: U32, +l0: U32, +l1: U32, +l2: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, p) = r
  dump.h0(N.ph(q, l0), h, l0, l1, l2, p, ls, ks)

def dump.w3(r: N.Q & U32, +ref: U32, +h: U32, +l0: U32, +l1: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +l2) = r
  dump.pay(N.q_pay(q, ref), h, l0, l1, l2, ls, ks)

def dump.w2(r: N.Q & U32, +ref: U32, +h: U32, +l0: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +l1) = r
  dump.w3(N.q_word(q, ref, 3), ref, h, l0, l1, ls, ks)

def dump.w1(r: N.Q & U32, +ref: U32, +h: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +l0) = r
  dump.w2(N.q_word(q, ref, 2), ref, h, l0, ls, ks)

def dump.live(live: Bool, q: N.Q, +ref: U32, +h: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  match live:
    case True{}:
      dump.w1(N.q_word(q, ref, 1), ref, h, ls, ks)
    case False{}:
      Dm{q, ls, ks}

def dump.hdr(r: N.Q & U32, +ref: U32, ls: List<&2, String>, ks: List<&2, U32>) -> Dm:
  (q, +h) = r
  dump.live(U32.is_ne(h, 0), q, ref, h, ls, ks)

def dump.slots(n: Nat, +page: U32, +slot: U32, d: Dm) -> Dm:
  match n:
    case 0n:
      d
    case 1n+p:
      match d:
        case Dm{q, ls, ks}:
          dump.slots(p, page, (slot + 1 : U32), dump.hdr(N.q_word(q, S.mk_ref(page, slot, 0), 0), S.mk_ref(page, slot, 0), ls, ks))

def dump.pages(n: Nat, +page: U32, d: Dm) -> Dm:
  match n:
    case 0n:
      d
    case 1n+p:
      dump.pages(p, (page + 1 : U32), dump.slots(S.cap(), page, 0, d))

def dump.start(r: S.Store & U32, rq: List<&2, N.Redex>, +itrs: U32, +errs: U32, +ser: U32) -> Dm:
  (st, +np) = r
  dump.pages(U32.to_nat(np), 0, Dm{N.Q{st, rq, itrs, errs, ser}, Nil{}, Nil{}})

# every live node, in store order, and their kinds
def dump(q: N.Q) -> Dm:
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      dump.start(S.st_pages(st), rq, itrs, errs, ser)

def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def count(ks: List<&2, U32>, +k: U32) -> U32:
  match ks:
    case Nil{}:
      0
    case Con{+x, t}:
      (count(t, k) + b2u(U32.is_eq(x, k)) : U32)

def census.show(+n: U32, +k: U32) -> String:
  match n:
    case 0:
      ""
    case _:
      " " ++ kname.k(k) ++ " " ++ U32.show(n)

def census.one(+ks: List<&2, U32>, +k: U32) -> String:
  census.show(count(ks, k), k)

def census(+ks: List<&2, U32>) -> String:
  "census:" ++ census.one(ks, 1) ++ census.one(ks, 2) ++ census.one(ks, 3) ++ census.one(ks, 4) ++
    census.one(ks, 5) ++ census.one(ks, 6) ++ census.one(ks, 7) ++ census.one(ks, 8) ++ census.one(ks, 9)

# Running
# =======

def start.root(r: N.Q & U32, +x: U32) -> N.Q & U32:
  (q, +root) = r
  (N.link(q, root, x), root)

# a template's net, its exposed port linked to a root
def start(r: N.Q & U32) -> N.Q & U32:
  (q, +x) = r
  start.root(N.node(q, R.KRoot{}, V.PNone{}), x)

def show_val(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      "value " ++ val_str(v)
    case None{}:
      "no value yet"

def counts(q: N.Q) -> String:
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++
        Nat.show(List.length(&2, N.Redex, rq)) ++ " active pairs left, " ++ U32.show(ser) ++ " nodes made"

def nodes_text(d: Dm, +head: String) -> String:
  match d:
    case Dm{q, ls, +ks}:
      head ++ "\n" ++ counts(q) ++ "\n" ++ census(ks) ++ "\nlive nodes:\n" ++ String.join(List.reverse(&2, String, ls), "\n")

def finish.val(r: N.Q & Maybe<&2, V.Val>) -> String:
  (q, v) = r
  nodes_text(dump(q), show_val(v))

def finish(tr: N.Tr, +root: U32, +from: U32) -> String:
  match tr:
    case N.Tr{q, log}:
      String.join(ev_lines(List.reverse(&2, N.Ev, log), from), "\n") ++ "\n" ++ finish.val(T.result((q, root)))

def go.run(r: N.Q & U32, +steps: Nat, +from: U32) -> String:
  (q, +root) = r
  finish(N.reduce_log(steps, N.Tr{q, Nil{}}), root, from)

# run t for at most `steps` interactions, listing those from `from` on
def trace(t: T.Tpl, +name: String, +steps: Nat, +from: U32) -> String:
  "net " ++ name ++ ", at most " ++ Nat.show(steps) ++ " interactions\n" ++
    go.run(start(T.instantiate(N.q_new(), t, 1)), steps, from)

def nat_of(+s: String) -> Nat:
  U32.to_nat(Maybe.default(&2, U32, U32.read(s), 0))

def u32_of(+s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)
