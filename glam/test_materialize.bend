import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/kernel.bend as K
import ../spike/knet.bend as KN
import ../spike/kstrat.bend as KS
import ../spike/kdemand.bend as KD
import ./materialize.bend as M

# Live templates end to end (the Cells plan's
# cells-freeze.cursors.materialize): a host applies a copy of a live
# source, a negative cursor at the source's interface in a ring of its
# own, to arguments, and is demanded; each time demand stops at a cursor,
# it is served from the source, and demand runs again. The value must be
# what applying the function gives:
# - `\x -> (\y -> y) x` applied to 7: the zero-node serve, the result
#   joined to the variable's cursor, so 7;
# - `\x -> (\y -> \z -> y) x` applied to 7 then 8: a value materialized
#   whose body joins the variable's cursor, so 7;
# - `\x -> (\y -> \z -> z) x` applied to 7: a function;
# - an erased source applied to 7, its root a static eraser or an eraser
#   node (what an eraser event leaves facing the interface): void alike,
#   the eraser node served as the static is (Splice_2026-11-19.md, S1;
#   copied, its statics pass read a word the pop left and wrote a header
#   word, and the host stuck);
# - `\x -> void`, its variable and body facing eraser nodes, applied to
#   7: void, the eraser nodes copied as statics.
# Run by scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_materialize.bend

def fn() -> T.TNode:
  T.TN{R.KFn{}, V.PNone{}}

def ap() -> T.TNode:
  T.TN{R.KAp{}, V.PNone{}}

def era() -> T.TNode:
  T.TN{R.KEraN{}, V.PNone{}}

def cur() -> T.TNode:
  T.TN{R.KCur{}, V.PNone{}}

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

def ln(+a: U32, +p: U32, +b: U32, +q: U32) -> T.TLink:
  T.TL{T.TE{a, p}, T.TE{b, q}}

# sources
def id_redex() -> T.Tpl:
  T.Tpl{[fn(), ap(), fn()], [ln(0, 1, 1, 2), ln(1, 0, 2, 0), ln(1, 1, 0, 2), ln(2, 1, 2, 2)], T.TE{0, 0}, 3}

def k_redex() -> T.Tpl:
  T.Tpl{[fn(), ap(), fn(), fn(), era()],
    [ln(0, 1, 1, 2), ln(1, 0, 2, 0), ln(1, 1, 0, 2), ln(2, 1, 3, 0), ln(3, 1, 2, 2), ln(3, 2, 4, 0)], T.TE{0, 0}, 5}

def const_redex() -> T.Tpl:
  T.Tpl{[fn(), ap(), fn(), fn(), era()],
    [ln(0, 1, 1, 2), ln(1, 0, 2, 0), ln(1, 1, 0, 2), ln(2, 1, 3, 0), ln(2, 2, 4, 0), ln(3, 1, 3, 2)], T.TE{0, 0}, 5}

# hosts: the copy, a negative cursor (node 0, base 32) at the source's
# interface (28), its situating node (node 1, base 36) with a static at
# its port, applied to one argument or two
def host1(+a: U32) -> T.Tpl:
  T.Tpl{[cur(), cur(), era(), ap(), num(a)], [ln(1, 0, 2, 0), ln(3, 0, 0, 0), ln(3, 1, 4, 0)], T.TE{3, 2}, 5}

def host2(+a: U32, +b: U32) -> T.Tpl:
  T.Tpl{[cur(), cur(), era(), ap(), num(a), ap(), num(b)],
    [ln(1, 0, 2, 0), ln(3, 0, 0, 0), ln(3, 1, 4, 0), ln(5, 0, 3, 2), ln(5, 1, 6, 0)], T.TE{5, 2}, 7}

# the ring made: the situating node at offset 0 for source 0, the
# cursor at position 28
def ring(h: P.H) -> P.H:
  P.wr(P.wr(P.wr(P.wr(P.wr(h, 36, P.hd2(18, 2, 0)), 38, 0), 39, 32), 34, 28), 35, 36)

# the loop: the source, the host, what it ended in, whether it has
type Rn is Type:
  Rn{s: P.H, h: P.H, out: String, done: Bool}

def val.v(r: P.H & V.Val) -> String:
  (h, v) = r
  match v:
    case V.VNum{+n}:
      U32.show(n)
    case _:
      "data"

def val.w(r: P.H & U32, +hd: U32) -> String:
  (h, +w) = r
  val.v(P.peek(h, P.form(hd), P.fld(hd), w))

def val.k(+k: U32, h: P.H, +b: U32, +hd: U32) -> String:
  match k:
    case 5:
      val.w(P.rd(h, (b + 2 : U32)), hd)
    case 1:
      "fn"
    case _:
      "kind " ++ U32.show(k)

def val.hd(r: P.H & U32, +b: U32) -> String:
  (h, +hd) = r
  val.k(P.rk(hd), h, b, hd)

def val.q(r: P.H & U32) -> String:
  (h, +q) = r
  val.hd(P.rd(h, P.base(q)), P.base(q))

# the value the host's interface faces
def value(h: P.H) -> String:
  val.q(P.rd(h, 29))

def st_of(d: KD.D) -> U32:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      st

def d_h(d: KD.D) -> P.H:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      h

def rn.stop(d: KD.D, h: P.H) -> Rn:
  match d:
    case KD.D{s, path, +top, +depth, +n, +st}:
      Rn{s, h, "stop in the source: " ++ K.st_name(st), True{}}

def rn.sv(v: M.Sv) -> Rn:
  match v:
    case M.SvOk{s, h, +n, +m}:
      Rn{s, h, "", False{}}
    case M.SvStop{d, h, +n}:
      rn.stop(d, h)
    case M.SvCur{s, h, +x, +n}:
      Rn{s, h, "a cursor of the source at " ++ U32.show(x), True{}}

def rn.need(r: P.H & U32, s: P.H) -> Rn:
  (h, +c) = r
  rn.sv(M.serve(s, h, c, 16n, 1000n))

def rn.st(+st: U32, h: P.H, +top: U32, s: P.H) -> Rn:
  match st:
    case 1:
      Rn{s, P.h_new(), value(h), True{}}
    case 2:
      rn.need(KS.d.at(h, top), s)
    case _:
      Rn{s, h, "stop " ++ K.st_name(st), True{}}

def rn.d(d: KD.D, s: P.H) -> Rn:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      rn.st(st, h, top, s)

def rn.step(s: P.H, h: P.H) -> Rn:
  rn.d(K.demand_ev(0, 2000n, KS.d.start(h)), s)

def rn.go(g: Nat, r: Rn) -> Rn:
  match g:
    case 0n:
      r
    case 1n+k:
      match r:
        case Rn{s, h, out, done}:
          match done:
            case True{}:
              Rn{s, h, out, True{}}
            case False{}:
              rn.go(k, rn.step(s, h))

def rn.out(r: Rn) -> String:
  match r:
    case Rn{s, h, out, done}:
      out

def applied.h(s: P.H, host: T.Tpl) -> String:
  rn.out(rn.go(16n, Rn{s, ring(KN.load(host)), "", False{}}))

def applied(src: T.Tpl, host: T.Tpl) -> String:
  applied.h(KN.load(src), host)

# an erased source: its root a static eraser, as the loader makes one
def erased() -> T.Tpl:
  T.Tpl{[era()], [], T.TE{0, 0}, 1}

# and its interface facing an eraser node instead
def era_node.l(r: P.H & U32) -> P.H:
  (h, +e) = r
  P.link(h, P.iface(), e)

def era_node() -> P.H:
  era_node.l(P.node(KN.load(id_redex()), P.hd(6, 0), 0))

# a function whose variable and body face eraser nodes, `\x -> void` as
# rules leave it: served, its eraser nodes read back as nodes, each made
# static in the copy as it is linked
# (cells-freeze.nested.host.splice.single)
def fn_void.b(r: P.H & U32, +f: U32) -> P.H:
  (h, +e) = r
  P.link(h, (f + 2 : U32), e)

def fn_void.v(r: P.H & U32, +f: U32) -> P.H:
  (h, +e) = r
  fn_void.b(P.node(P.link(h, (f + 1 : U32), e), P.hd(6, 0), 0), f)

def fn_void.f(r: P.H & U32) -> P.H:
  (h, +f) = r
  fn_void.v(P.node(h, P.hd(6, 0), 0), f)

def fn_void() -> P.H:
  fn_void.f(P.rd(KN.load(T.Tpl{[fn()], [], T.TE{0, 0}, 1}), (P.iface() + 1 : U32)))

def check.k(+same: Bool, got: String, want: String, name: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      name ++ ": got " ++ got ++ ", want " ++ want ++ "\n"

def check(+got: String, +want: String, name: String) -> String:
  check.k(String.eq(got, want), got, want, name)

def report.k(+none: Bool, s: String) -> String:
  match none:
    case True{}:
      "ok"
    case False{}:
      s

def report(+s: String) -> String:
  report.k(String.eq(s, ""), s)

# A climb that found no position of the ring, which only corruption
# reaches: the host's error raised, nothing copied
# (docs/reviews/Freeze_2026-11-21.md, B4)
def climb_err.k(r: P.H & P.HS, +m: U32) -> String:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      "errs " ++ U32.show(errs) ++ " copied " ++ U32.show(m)

def climb_err.v(v: M.Sv) -> String:
  match v:
    case M.SvOk{s, h, +n, +m}:
      climb_err.k(P.stats(h), m)
    case M.SvStop{d, h, +n}:
      "stop"
    case M.SvCur{s, h, +x, +n}:
      "cursor"

def climb_err(+t: T.Tpl) -> String:
  climb_err.v(M.sv.climbed(M.Cl{KN.load(t), KN.load(t), 32, False{}}, 0, 0, 0, 0))

def main() -> String:
  report(
    check(climb_err(id_redex()), "errs 1 copied 0", "a failed climb") ++
    check(applied(id_redex(), host1(7)), "7", "id_redex 7") ++
    check(applied(k_redex(), host2(7, 8)), "7", "k_redex 7 8") ++
    check(applied(const_redex(), host1(7)), "fn", "const_redex 7") ++
    check(applied(erased(), host1(7)), "stop a void", "erased 7") ++
    check(applied.h(era_node(), host1(7)), "stop a void", "eraser node 7") ++
    check(applied.h(fn_void(), host1(7)), "stop a void", "fn_void 7"))
