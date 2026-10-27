import Base
import ./val.bend as V
import ./rules.bend as R
import ./store.bend as S
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X

# Runs a test net for at most <steps> interactions through the reducer's
# own interaction function, printing each interaction as it met it, then
# the result and every live node.
#
#   trace <net> <steps>     nets: pow22 pow33 pow23 pow32 two_two_two
#                                 self2 self3 chain5
#
# An interaction line: its number, the negative node then the positive one
# (kind, node, payload: a fan's label as site.inst), the rule taken, and
# the redex's external peers (A's ports 1, 2, then B's). A node line: the
# node and its ports' peers. A reference prints as n<slot>.<port>, with
# p<page>: before it past page 0.

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

def page_str(+p: U32) -> String:
  match p:
    case 0:
      ""
    case _:
      "p" ++ U32.show(p) ++ ":"

def node_str(+r: U32) -> String:
  "n" ++ page_str(S.ref_page(r)) ++ U32.show(S.ref_slot(r))

def ref_str.go(nil: Bool, +r: U32) -> String:
  match nil:
    case True{}:
      "-"
    case False{}:
      node_str(r) ++ "." ++ U32.show(S.ref_port(r))

def ref_str(+r: U32) -> String:
  ref_str.go(U32.is_eq(r, S.nil()), r)

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

def ext_str(+x: N.Ext) -> String:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      ref_str(e0) ++ " " ++ ref_str(e1) ++ " | " ++ ref_str(e2) ++ " " ++ ref_str(e3)

def ev_line(ev: N.Ev) -> String:
  match ev:
    case N.Ev{+i, +a, +b, +ha, +hb, +pa, +pb, +x}:
      "#" ++ U32.show(i) ++ "  " ++ kname(ha) ++ " " ++ node_str(a) ++ pay_str(pa) ++ " >< " ++
        kname(hb) ++ " " ++ node_str(b) ++ pay_str(pb) ++ "  " ++
        rule_name(N.kof((ha .&. 15 : U32)), N.kof((hb .&. 15 : U32)), N.rule_test(N.kof((ha .&. 15 : U32)), N.kof((hb .&. 15 : U32)), pa, pb)) ++
        "  ext " ++ ext_str(x)

def ev_lines(evs: List<&2, N.Ev>) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      ev_line(e) <> ev_lines(t)

# The live nodes
# ==============

type Dm is Type:
  Dm{q: N.Q, ls: List<&2, String>}

def port_strs(n: Nat, +k: U32, +ls: List<&2, U32>) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "  " ++ U32.show(k) ++ ":" ++ ref_str(N.nth(ls, U32.to_nat(k))) ++ port_strs(p, (k + 1 : U32), ls)

def node_line(+ref: U32, +h: U32, +l0: U32, +l1: U32, +l2: U32, p: V.Pay) -> String:
  node_str(ref) ++ " " ++ kname(h) ++ pay_str(p) ++ port_strs(R.arity(N.kof((h .&. 15 : U32))), 0, [l0, l1, l2])

def dump.fin(r: N.Q & V.Pay, +ref: U32, +h: U32, +l0: U32, +l1: U32, +l2: U32, ls: List<&2, String>) -> Dm:
  (q, p) = r
  Dm{q, node_line(ref, h, l0, l1, l2, p) <> ls}

def dump.w3(r: N.Q & U32, +ref: U32, +h: U32, +l0: U32, +l1: U32, ls: List<&2, String>) -> Dm:
  (q, +l2) = r
  dump.fin(N.q_pay(q, ref), ref, h, l0, l1, l2, ls)

def dump.w2(r: N.Q & U32, +ref: U32, +h: U32, +l0: U32, ls: List<&2, String>) -> Dm:
  (q, +l1) = r
  dump.w3(N.q_word(q, ref, 3), ref, h, l0, l1, ls)

def dump.w1(r: N.Q & U32, +ref: U32, +h: U32, ls: List<&2, String>) -> Dm:
  (q, +l0) = r
  dump.w2(N.q_word(q, ref, 2), ref, h, l0, ls)

def dump.live(live: Bool, q: N.Q, +ref: U32, +h: U32, ls: List<&2, String>) -> Dm:
  match live:
    case True{}:
      dump.w1(N.q_word(q, ref, 1), ref, h, ls)
    case False{}:
      Dm{q, ls}

def dump.hdr(r: N.Q & U32, +ref: U32, ls: List<&2, String>) -> Dm:
  (q, +h) = r
  dump.live(U32.is_ne(h, 0), q, ref, h, ls)

def dump.slots(n: Nat, +page: U32, +slot: U32, d: Dm) -> Dm:
  match n:
    case 0n:
      d
    case 1n+p:
      match d:
        case Dm{q, ls}:
          dump.slots(p, page, (slot + 1 : U32), dump.hdr(N.q_word(q, S.mk_ref(page, slot, 0), 0), S.mk_ref(page, slot, 0), ls))

def dump.pages(n: Nat, +page: U32, d: Dm) -> Dm:
  match n:
    case 0n:
      d
    case 1n+p:
      dump.pages(p, (page + 1 : U32), dump.slots(S.cap(), page, 0, d))

def dump.start(r: S.Store & U32, rq: List<&2, N.Redex>, +itrs: U32, +errs: U32) -> Dm:
  (st, +np) = r
  dump.pages(U32.to_nat(np), 0, Dm{N.Q{st, rq, itrs, errs}, Nil{}})

# every live node, in store order
def dump(q: N.Q) -> Dm:
  match q:
    case N.Q{st, rq, +itrs, +errs}:
      dump.start(S.st_pages(st), rq, itrs, errs)

# Running
# =======

def start.root(r: N.Q & U32, +x: U32) -> N.Q & U32:
  (q, +root) = r
  (N.link(q, root, x), root)

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
    case N.Q{st, rq, +itrs, +errs}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++
        Nat.show(List.length(&2, N.Redex, rq)) ++ " active pairs left"

def nodes_text(d: Dm, +head: String) -> String:
  match d:
    case Dm{q, ls}:
      head ++ "\n" ++ counts(q) ++ "\nlive nodes:\n" ++ String.join(List.reverse(&2, String, ls), "\n")

def finish.val(r: N.Q & Maybe<&2, V.Val>) -> String:
  (q, v) = r
  nodes_text(dump(q), show_val(v))

def finish(tr: N.Tr, +root: U32) -> String:
  match tr:
    case N.Tr{q, log}:
      String.join(ev_lines(List.reverse(&2, N.Ev, log)), "\n") ++ "\n" ++ finish.val(T.result((q, root)))

def go.run(r: N.Q & U32, +steps: Nat) -> String:
  (q, +root) = r
  finish(N.reduce_log(steps, N.Tr{q, Nil{}}), root)

def net_of(+k: U32) -> T.Tpl:
  match k:
    case 0:
      X.t_pow(2, 2)
    case 1:
      X.t_pow(3, 3)
    case 2:
      X.t_pow(2, 3)
    case 3:
      X.t_pow(3, 2)
    case 4:
      X.t_two_two_two()
    case 5:
      X.t_self(2)
    case 6:
      X.t_self(3)
    case _:
      X.t_chain(5)

def pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def find(ns: List<&2, String>, +name: String, +i: U32) -> U32:
  match ns:
    case Nil{}:
      i
    case Con{n, t}:
      pick(String.eq(n, name), i, find(t, name, (i + 1 : U32)))

def names() -> List<&2, String>:
  ["pow22", "pow33", "pow23", "pow32", "two_two_two", "self2", "self3", "chain5"]

def go(+name: String, +steps: Nat) -> String:
  "net " ++ name ++ ", at most " ++ Nat.show(steps) ++ " interactions\n" ++
    go.run(start(T.instantiate(N.q_new(), net_of(find(names(), name, 0)), 1)), steps)

def steps_of(+s: String) -> Nat:
  U32.to_nat(Maybe.default(&2, U32, U32.read(s), 0))

def go.args(xs: List<String>) -> String:
  match xs:
    case Con{p, r}:
      match r:
        case Con{name, r2}:
          match r2:
            case Con{s, r3}:
              go(name, steps_of(s))
            case Nil{}:
              go(name, 0n)
        case Nil{}:
          "usage: trace <net> <steps>"
    case Nil{}:
      "usage: trace <net> <steps>"

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    IO.print(go.args(xs))
