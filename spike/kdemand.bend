# Written by Blend from kdemand.blend; do not edit.
# blend stamp: 52e1a411e187 f92da926bee66b8e
import Base
import ./val.bend as V
import ./net.bend as N
import ./kprim.bend as P
import ./krules.bend as KR
import ./knet.bend as KN
import ./kmem_grow.bend as KM
import ./kchain.bend as C
import ./rules.bend as Blend_1

# blend: kdemand.blend:42
type D is Type:
  D{h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32}

# blend: kdemand.blend:61
type Fw is Type:
  Fw{h: P.H, path: KM.M, +b: U32, +i: U32}

# blend: kdemand.blend:73
type Sc is Type:
  Sc{m: KM.M, +hit: Bool}

# blend: kdemand.blend:84
type Dn is Type:
  Dn{+go: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +q: U32}

# blend: kdemand.blend:45
def d.go(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  D{h, path, top, depth, n, 0}

# blend: kdemand.blend:48
def d.stop(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  D{h, path, top, depth, n, st}

# blend: kdemand.blend:87
def d.out(+st: U32) -> U32:
  match st:
    case 0:
      4
    case _:
      st

# blend: kdemand.blend:94
def d.end(d: D) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st}:
      D{h, path, top, depth, n, d.out(st)}

# blend: kdemand.blend:99
def fw.v(+pos: Bool, h: P.H, path: KM.M, +x: U32, +i: U32) -> Fw:
  match pos:
    case True{}:
      Fw{h, path, x, i}
    case False{}:
      Fw{h, path, 0, 0}

# blend: kdemand.blend:106
def fw.hx(r: P.H & U32, path: KM.M, +x: U32, +i: U32) -> Fw:
  (h, +hx) = r
  fw.v(Bool.not(KR.kind_neg(P.rk(hx))), h, path, x, i)

# blend: kdemand.blend:110
def fw.at(r: KM.M & U32, h: P.H, +i: U32) -> Fw:
  (path, +x) = r
  fw.hx(P.rd(h, x), path, x, i)

# blend: kdemand.blend:116
def fw.go(k: Nat, s: Fw, +i: U32) -> Fw:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Fw{h, path, +b, +j}:
          match b:
            case 0:
              fw.go(p, fw.at(KM.m_get(path, i), h, i), (i + 1 : U32))
            case _:
              Fw{h, path, b, j}

# blend: kdemand.blend:130
def fw.top(s: Fw, +top: U32, +depth: U32) -> Fw:
  match s:
    case Fw{h, path, +b, +j}:
      match b:
        case 0:
          fw.hx(P.rd(h, top), path, top, (depth + 1 : U32))
        case _:
          Fw{h, path, b, j}

# blend: kdemand.blend:141
def fw.end(s: Fw, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  match s:
    case Fw{h, path, +b, +i}:
      match b:
        case 0:
          D{h, path, top, depth, n, st}
        case _:
          D{h, path, b, (i - 1 : U32), n, 7}

# blend: kdemand.blend:151
def fw.scan(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  fw.end(fw.top(fw.go(U32.to_nat(depth), Fw{h, path, 0, 0}, 1), top, depth), top, depth, n, st)

# blend: kdemand.blend:154
def sc.step(r: KM.M & U32, +x: U32) -> Sc:
  (m, +v) = r
  Sc{m, U32.is_eq(v, x)}

# blend: kdemand.blend:159
def sc.run(k: Nat, s: Sc, +i: U32, +x: U32) -> Sc:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sc{m, +hit}:
          match hit:
            case True{}:
              Sc{m, True{}}
            case False{}:
              sc.run(p, sc.step(KM.m_get(m, i), x), (i + 1 : U32), x)

# blend: kdemand.blend:172
def wk.grown.go(ok: Bool, path: KM.M, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap2: U32) -> D:
  match ok:
    case True{}:
      d.go(h, KM.m_set(KM.m_set(path, 0, cap2), (depth + 1 : U32), top), x, (depth + 1 : U32), n)
    case False{}:
      d.stop(P.h_err(h), path, top, depth, n, 6)

# blend: kdemand.blend:180
def wk.grown(r: KM.M & U32, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  (path, +cap2) = r
  wk.grown.go(U32.is_gt(cap2, cap), path, h, top, depth, n, x, cap2)

# blend: kdemand.blend:184
def wk.seen(s: Sc, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  match s:
    case Sc{path, +hit}:
      match hit:
        case True{}:
          fw.scan(h, path, top, depth, n, 5)
        case False{}:
          wk.grown(KM.m_ensure(path, (cap * 2 : U32), cap, P.w_maxd()), h, top, depth, n, x, cap)

# blend: kdemand.blend:193
def wk.full.go(full: Bool, path: KM.M, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  match full:
    case True{}:
      wk.seen(sc.run(U32.to_nat(depth), Sc{path, False{}}, 1, top), h, top, depth, n, x, cap)
    case False{}:
      d.go(h, KM.m_set(path, (depth + 1 : U32), top), x, (depth + 1 : U32), n)

# blend: kdemand.blend:200
def wk.full(r: KM.M & U32, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32) -> D:
  (path, +cap) = r
  wk.full.go(U32.is_ge((depth + 1 : U32), cap), path, h, top, depth, n, x, cap)

# blend: kdemand.blend:205
def wk.push(p2: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +x: U32) -> D:
  match p2:
    case True{}:
      wk.full(KM.m_get(path, 0), h, top, depth, n, x)
    case False{}:
      d.go(h, KM.m_set(path, (depth + 1 : U32), top), x, (depth + 1 : U32), n)

# blend: kdemand.blend:218
def Demand.Res() -> Type: P.H

# blend: kdemand.blend:455
def Demand.after(h: Demand.Res(), +x: N.Ext) -> Demand.Res():
  h

# blend: kdemand.blend:217
def Demand.S() -> Type: Unit

# blend: kdemand.blend:219
def Demand.note(u: Demand.S(), +x: U32, +y: U32) -> Demand.S():
  u

# blend: kdemand.blend:221
def Demand.fin(h: P.H, u: Demand.S()) -> Demand.Res():
  h

# blend: kdemand.blend:223
def Demand.wd(w: KN.Wd, u: Demand.S()) -> Demand.Res():
  KN.wd.h(w)

# blend: kdemand.blend:225
def Demand.erased(h: Demand.Res(), +x: N.Ext) -> Demand.Res():
  KN.ev.settle(h, x)

# blend: kdemand.blend:228
def Demand.wk.pop.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  d.go(h, path, p, (depth - 1 : U32), n)

# blend: kdemand.blend:232
def Demand.wk.pop(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      Demand.wk.pop.r(KM.m_get(path, depth), h, depth, n)

# blend: kdemand.blend:239
def Demand.wk.past(gone: Bool, h: P.H, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      Demand.wk.pop(h, path, depth, n)
    case False{}:
      d.go(h, path, p, depth, n)

# blend: kdemand.blend:246
def Demand.wk.hp(r: P.H & U32, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  (h, +hp) = r
  Demand.wk.past(U32.is_eq(hp, 0), h, path, p, depth, n)

# blend: kdemand.blend:256
def Demand.wk.back.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  Demand.wk.hp(P.rd(h, p), path, p, (depth - 1 : U32), n)

# blend: kdemand.blend:260
def Demand.wk.back(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      Demand.wk.back.r(KM.m_get(path, depth), h, depth, n)

# blend: kdemand.blend:267
def Demand.wk.hb.go(gone: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      Demand.wk.back(h, path, depth, (n + 1 : U32))
    case False{}:
      fw.scan(h, path, top, depth, n, 3)

# blend: kdemand.blend:274
def Demand.wk.hb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +hb) = r
  Demand.wk.hb.go(U32.is_eq(hb, 0), h, path, top, depth, n)

# blend: kchain.blend:25
def Demand.go.gen(+rn: U32, +t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite(~Demand.S(), ~Demand.Res(), ~Demand.note, ~Demand.fin, ~Demand.after, ~Demand.erased, P.rk(ha), rn, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# blend: kchain.blend:70
def Demand.go.id(+t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite_id(~Demand.S(), ~Demand.Res(), ~Demand.note, ~Demand.fin, ~Demand.after, ~Demand.erased, P.rk(ha), t, h, st, a, b, ha, hb, pa, pb, e0, e1, P.nil(), P.nil())

# blend: kchain.blend:39
def Demand.go.wd.w(+er: Bool, w: KN.Wd, st: Demand.S()) -> Demand.Res():
  match er w:
    case True{} KN.Wd{h, ns, +sx}:
      Demand.erased(Demand.wd(KN.Wd{h, ns, sx}, st), sx)
    case False{} KN.Wd{h, ns, +sx}:
      Demand.after(Demand.wd(KN.Wd{h, ns, sx}, st), sx)

# blend: kchain.blend:32
def Demand.rule_erases(r: Blend_1.Rule) -> Bool:
  match r:
    case Blend_1.RWire{xs, ls}:
      Blend_1.nv.any(xs)
    case Blend_1.RStuck{}:
      False{}

# blend: kchain.blend:48
def Demand.go.wd(r: Blend_1.Rule, w: KN.Wd, st: Demand.S()) -> Demand.Res():
  Demand.go.wd.w(Demand.rule_erases(r), w, st)

# blend: kchain.blend:79
def Demand.go.interp.id(+t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      Demand.go.wd(Blend_1.rule_id(KN.kof(ha), t), KN.apply_rule(Blend_1.rule_id(KN.kof(ha), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, N.Ext4{e0, e1, P.nil(), P.nil()}), st)

# blend: kchain.blend:51
def Demand.go.interp.pl(r: P.Pl, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> Demand.Res():
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      Demand.go.wd(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KN.apply_rule(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), h, a, b, ha, hb, pa, pb, N.Ext4{e0, e1, e2, e3}), st)

# blend: kchain.blend:59
def Demand.go.interp(ctl: Bool, +t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match ctl:
    case True{}:
      match x:
        case N.Ext4{+e0, +e1, +e2, +e3}:
          Demand.go.interp.pl(P.peel_ctl(KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case False{}:
      Demand.go.wd(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KN.apply_rule(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, x), st)

# blend: kchain.blend:88
def Demand.go.loop(+id: Bool, +fast: Bool, +t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match id fast:
    case True{} True{}:
      Demand.go.id(t, h, st, a, b, ha, hb, pa, pb, x)
    case True{} False{}:
      Demand.go.interp.id(t, h, st, a, b, ha, hb, pa, pb, x)
    case False{} _:
      Demand.go.interp(U32.is_eq(P.rk(ha), 10) && U32.is_eq(P.rk(hb), 11), t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:99
def Demand.is_id(+x: N.Ext, +a: U32, +b: U32, +hb: U32) -> Bool:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      U32.is_eq(P.rk(hb), 1) && U32.is_eq(e2, (b + 2 : U32)) && U32.is_eq(e3, (b + 1 : U32)) && Bool.not(KN.own(e0, a, b) || KN.own(e1, a, b))

# blend: kchain.blend:104
def Demand.go.which(gen: Bool, +fast: Bool, +rn: U32, +t: Bool, h: P.H, st: Demand.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  match gen:
    case True{}:
      Demand.go.gen(rn, t, h, st, a, b, ha, hb, pa, pb, x)
    case False{}:
      Demand.go.loop(Demand.is_id(x, a, b, hb), fast, t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:113
def Demand.go.rule(r: P.H & Bool, st: Demand.S(), +fast: Bool, +rn: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> Demand.Res():
  (h, +t) = r
  Demand.go.which(fast && Bool.not(KN.any_partner(x, a, b)), fast, rn, t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:117
def Demand.go.ext.r(+rn: U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: Demand.S()) -> Demand.Res():
  Demand.go.rule(KR.test(~Demand.S(), ~Demand.Res(), ~Demand.note, ~Demand.fin, ~Demand.after, ~Demand.erased, rn, h, ha, hb, KN.payload(ha, 0, a2), KN.payload(hb, b1, b2)), st, fast, rn, a, b, ha, hb, KN.payload(ha, 0, a2), KN.payload(hb, b1, b2),
    N.Ext4{KN.aux_or_nil(U32.is_lt(1, KN.arity(ha)), a1), KN.aux_or_nil(U32.is_lt(2, KN.arity(ha)), a2),
      KN.aux_or_nil(U32.is_lt(1, KN.arity(hb)), b1), KN.aux_or_nil(U32.is_lt(2, KN.arity(hb)), b2)})

# blend: kchain.blend:125
def Demand.go.ext(+fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: Demand.S()) -> Demand.Res():
  Demand.go.ext.r(KR.rule_no(P.rk(ha), P.rk(hb)), fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

# blend: kchain.blend:128
def Demand.go.b2(r: P.H & U32, st: Demand.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32) -> Demand.Res():
  (h, +b2) = r
  Demand.go.ext(fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

# blend: kchain.blend:132
def Demand.go.b1(r: P.H & U32, st: Demand.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32) -> Demand.Res():
  (h, +b1) = r
  Demand.go.b2(P.rd(h, (b + 3 : U32)), st, fast, a, b, ha, hb, a1, a2, b1)

# blend: kchain.blend:136
def Demand.go.a2(r: P.H & U32, st: Demand.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32) -> Demand.Res():
  (h, +a2) = r
  Demand.go.b1(P.rd(h, (b + 2 : U32)), st, fast, a, b, ha, hb, a1, a2)

# blend: kchain.blend:140
def Demand.go.a1(r: P.H & U32, st: Demand.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> Demand.Res():
  (h, +a1) = r
  Demand.go.a2(P.rd(h, (a + 3 : U32)), st, fast, a, b, ha, hb, a1)

# blend: kchain.blend:146
def Demand.go(h: P.H, st: Demand.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> Demand.Res():
  Demand.go.a1(P.rd(h, (a + 2 : U32)), st, fast, a, b, ha, hb)

# blend: kdemand.blend:284
def Demand.wk.rw(+sb: U32, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match sb:
    case 0:
      Demand.wk.back(Demand.go(h, Unit{}, True{}, a, b, ha, hb), path, depth, (n + 1 : U32))
    case 1:
      fw.scan(h, path, top, depth, n, 3)
    case _:
      Demand.wk.hb(P.rd(Demand.go(h, Unit{}, True{}, a, b, ha, hb), b), path, top, depth, n)

# blend: kdemand.blend:293
def Demand.nd.lz(z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match z:
    case P.Lz{h, +lazy, +k}:
      match lazy:
        case True{}:
          D{h, path, top, depth, n, 2}
        case False{}:
          Demand.wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:302
def Demand.nd.pb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  (h, +pb) = r
  Demand.nd.lz(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:306
def Demand.nd.go(chk: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match chk:
    case True{}:
      Demand.nd.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, a, b, ha, hb)
    case False{}:
      Demand.wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:314
def Demand.may_need(+ha: U32, +hb: U32) -> Bool:
  (U32.is_eq(P.rk(ha), 2) || U32.is_eq(P.rk(ha), 9)) && U32.is_eq(P.rk(hb), 5) && U32.is_eq(P.form(hb), 0)

# blend: kdemand.blend:320
def Demand.wk.ori(neg: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +x: U32, +y: U32, +hx: U32, +hy: U32) -> D:
  match neg:
    case True{}:
      Demand.nd.go(Demand.may_need(hx, hy), h, path, top, depth, n, x, y, hx, hy)
    case False{}:
      fw.scan(h, path, top, depth, n, 7)

# blend: kdemand.blend:327
def Demand.wk.hy(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32, +hx: U32) -> D:
  (h, +hy) = r
  Demand.wk.ori(KR.kind_neg(P.rk(hx)), h, path, top, depth, n, top, y, hx, hy)

# blend: kdemand.blend:331
def Demand.wk.hx(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hx) = r
  Demand.wk.hy(P.rd(h, y), path, top, depth, n, y, hx)

# blend: kdemand.blend:339
def Demand.wk.root.v(+void: Bool, h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match void:
    case True{}:
      d.stop(h, path, 0, depth, n, 8)
    case False{}:
      d.stop(h, path, 0, depth, n, 1)

# blend: kchain.blend:251
def Demand.static_meet(h: P.H, st: Demand.S()) -> Demand.Res():
  Demand.fin(h, st)

# blend: kchain.blend:174
def Demand.se.put.go(+skip: Bool, h: P.H, +e: U32, +s: U32) -> P.H:
  match skip:
    case True{}:
      h
    case False{}:
      P.wr(h, (e + 1 : U32), s)

# blend: kchain.blend:182
def Demand.se.put(h: P.H, +e: U32, +s: U32, +x: U32) -> P.H:
  Demand.se.put.go(P.is_static(e) || U32.is_eq(P.base(e), x), h, e, s)

# blend: kchain.blend:192
def Demand.se.note(+none: Bool, st: Demand.S(), +e: U32, +s: U32) -> Demand.S():
  match none:
    case True{}:
      st
    case False{}:
      Demand.note(st, e, s)

# blend: kchain.blend:203
def Demand.se.notes(+loop: Bool, st: Demand.S(), +k: U32, +e1: U32, +e2: U32) -> Demand.S():
  match loop:
    case True{}:
      Demand.note(st, P.era(), P.era())
    case False{}:
      Demand.se.note(U32.is_lt(KR.kind_arity(k), 3), Demand.se.note(U32.is_lt(KR.kind_arity(k), 2), st, e1, P.era()), e2, P.era())

# blend: kchain.blend:210
def Demand.se.do(h: P.H, st: Demand.S(), +x: U32, +k: U32, +e1: U32, +e2: U32) -> Demand.Res():
  Demand.erased(Demand.fin(Demand.se.put(Demand.se.put(h, e1, P.era(), x), e2, P.era(), x),
      Demand.se.notes(Bool.not(P.is_static(e1)) && U32.is_eq(P.base(e1), x), st, k, e1, e2)),
    N.Ext4{e1, e2, P.nil(), P.nil()})

# blend: kchain.blend:185
def Demand.se.free(+data: Bool, h: P.H, +x: U32, +hx: U32, +w2: U32, +w3: U32) -> P.H:
  match data:
    case True{}:
      P.free(P.drop(h, P.form(hx), KN.payload(hx, w2, w3)), x)
    case False{}:
      P.free(h, x)

# blend: kchain.blend:224
def Demand.se.go(+ok: Bool, +stuck: Bool, h: P.H, st: Demand.S(), +x: U32, +hx: U32, +k: U32, +w2: U32, +w3: U32) -> Demand.Res():
  match ok stuck:
    case True{} False{}:
      Demand.se.do(Demand.se.free(KR.is_data(P.rk(hx)), h, x, hx, w2, w3), st, x, k,
        KN.aux_or_nil(U32.is_lt(1, KR.kind_arity(k)), w2), KN.aux_or_nil(U32.is_lt(2, KR.kind_arity(k)), w3))
    case True{} True{}:
      Demand.fin(h, st)
    case False{} _:
      Demand.fin(P.h_err(h), st)

# blend: kchain.blend:217
def Demand.se.stuck(+neg: Bool, +k: U32) -> U32:
  match neg:
    case True{}:
      KR.stuck_by(k, 7)
    case False{}:
      KR.stuck_by(6, k)

# blend: kchain.blend:234
def Demand.se.k(+k: U32, h: P.H, st: Demand.S(), +x: U32, +s: U32, +hx: U32, +w2: U32, +w3: U32) -> Demand.Res():
  Demand.se.go(U32.is_eq(s, P.era()), U32.is_ne(Demand.se.stuck(KR.kind_neg(k), k), 0), h, st, x, hx, k, w2, w3)

# blend: kchain.blend:237
def Demand.se.w3(r: P.H & U32, st: Demand.S(), +x: U32, +s: U32, +hx: U32, +w2: U32) -> Demand.Res():
  (h, +w3) = r
  Demand.se.k(P.rk(hx), h, st, x, s, hx, w2, w3)

# blend: kchain.blend:241
def Demand.se.w2(r: P.H & U32, st: Demand.S(), +x: U32, +s: U32, +hx: U32) -> Demand.Res():
  (h, +w2) = r
  Demand.se.w3(P.rd(h, (x + 3 : U32)), st, x, s, hx, w2)

# blend: kchain.blend:245
def Demand.se.hx(r: P.H & U32, st: Demand.S(), +x: U32, +s: U32) -> Demand.Res():
  (h, +hx) = r
  Demand.se.w2(P.rd(h, (x + 2 : U32)), st, x, s, hx)

# blend: kchain.blend:256
def Demand.static_erase(h: P.H, st: Demand.S(), +x: U32, +s: U32) -> Demand.Res():
  Demand.se.hx(P.rd(h, x), st, x, s)

# blend: kchain.blend:259
def Demand.int.st(+sx: Bool, h: P.H, st: Demand.S(), +x: U32, +y: U32) -> Demand.Res():
  match sx:
    case True{}:
      Demand.static_meet(h, st)
    case False{}:
      Demand.static_erase(h, st, x, y)

# blend: kchain.blend:149
def Demand.ori(neg: Bool, h: P.H, st: Demand.S(), +fast: Bool, +x: U32, +y: U32, +hx: U32, +hy: U32) -> Demand.Res():
  match neg:
    case True{}:
      Demand.go(h, st, fast, x, y, hx, hy)
    case False{}:
      Demand.go(h, st, fast, y, x, hy, hx)

# blend: kchain.blend:156
def Demand.int.y(r: P.H & U32, st: Demand.S(), +fast: Bool, +x: U32, +y: U32, +hx: U32) -> Demand.Res():
  (h, +hy) = r
  Demand.ori(KR.kind_neg(P.rk(hx)), h, st, fast, x, y, hx, hy)

# blend: kchain.blend:160
def Demand.int.x(r: P.H & U32, st: Demand.S(), +fast: Bool, +x: U32, +y: U32) -> Demand.Res():
  (h, +hx) = r
  Demand.int.y(P.rd(h, y), st, fast, x, y, hx)

# blend: kchain.blend:266
def Demand.int.s(+sy: Bool, h: P.H, st: Demand.S(), +fast: Bool, +x: U32, +y: U32) -> Demand.Res():
  match sy:
    case True{}:
      Demand.int.st(P.is_static(x), h, st, x, y)
    case False{}:
      Demand.int.x(P.rd(h, x), st, fast, x, y)

# blend: kchain.blend:277
def Demand.interact.f(h: P.H, st: Demand.S(), +fast: Bool, +x: U32, +y: U32) -> Demand.Res():
  Demand.int.s(U32.is_eq(((x .|. y : U32) .&. 3 : U32), 3), h, st, fast, x, y)

# blend: kdemand.blend:346
def Demand.wk.root.go(c: Bool, +void: Bool, h: P.H, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  match c:
    case True{}:
      d.go(Demand.interact.f(h, Unit{}, True{}, P.iface(), y), path, P.iface(), depth, (n + 1 : U32))
    case False{}:
      Demand.wk.root.v(void, h, path, depth, n)

# blend: kdemand.blend:353
def Demand.wk.root(r: P.H & U32, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hy) = r
  Demand.wk.root.go(U32.is_eq(P.rk(hy), 11), U32.is_eq(P.rk(hy), 7), h, path, depth, n, y)

# blend: kdemand.blend:357
def Demand.wk.pair(root: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  match root:
    case True{}:
      Demand.wk.root(P.rd(h, y), path, depth, n, y)
    case False{}:
      Demand.wk.hx(P.rd(h, top), path, top, depth, n, y)

# blend: kdemand.blend:368
def Demand.wk.sn(+neg: Bool, +stuck: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match neg stuck:
    case True{} False{}:
      Demand.wk.back(Demand.static_erase(h, Unit{}, top, q), path, depth, (n + 1 : U32))
    case True{} True{}:
      fw.scan(h, path, top, depth, n, 3)
    case False{} _:
      fw.scan(h, path, top, depth, n, 7)

# blend: kdemand.blend:377
def Demand.wk.sx(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  (h, +hx) = r
  Demand.wk.sn(KR.kind_neg(P.rk(hx)), U32.is_ne(KN.se.stuck(KR.kind_neg(P.rk(hx)), P.rk(hx)), 0), h, path, top, depth, n, q)

# blend: kdemand.blend:382
def Demand.wk.sr(+root: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match root:
    case True{}:
      Demand.wk.root.v(U32.is_eq(q, P.era()), h, path, depth, n)
    case False{}:
      Demand.wk.sx(P.rd(h, top), path, top, depth, n, q)

# blend: kdemand.blend:389
def Demand.wk.q.go(st: Bool, +pr: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match st pr:
    case True{} _:
      Demand.wk.sr(U32.is_eq(top, P.iface()), h, path, top, depth, n, q)
    case False{} True{}:
      Demand.wk.pair(U32.is_eq(top, P.iface()), h, path, top, depth, n, q)
    case False{} False{}:
      wk.push(U32.is_eq(((depth + 1 : U32) .&. depth : U32), 0), h, path, top, depth, n, P.base(q))

# blend: kdemand.blend:400
def Demand.dn.can(+q: U32, +depth: U32) -> Bool:
  Bool.not(P.pri(q)) && U32.is_ne(((depth + 1 : U32) .&. depth : U32), 0)

# blend: kdemand.blend:403
def Demand.dn.r(r: P.H & U32, path: KM.M, +x: U32, +depth: U32) -> Dn:
  (h, +q) = r
  Dn{Demand.dn.can(q, depth), h, path, x, depth, q}

# blend: kdemand.blend:407
def Demand.dn.step(h: P.H, path: KM.M, +top: U32, +depth: U32, +q: U32) -> Dn:
  Demand.dn.r(P.rd(h, (P.base(q) + 1 : U32)), KM.m_set(path, (depth + 1 : U32), top), P.base(q), (depth + 1 : U32))

# blend: kdemand.blend:410
def Demand.wk.down(f: Nat, s: Dn) -> Dn:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case Dn{+more, h, path, +top, +depth, +q}:
          match more:
            case True{}:
              Demand.wk.down(g, Demand.dn.step(h, path, top, depth, q))
            case False{}:
              Dn{False{}, h, path, top, depth, q}

# blend: kdemand.blend:423
def Demand.wk.c(s: Dn, +n: U32) -> D:
  match s:
    case Dn{+more, h, path, +top, +depth, +q}:
      Demand.wk.q.go(P.is_static(q), U32.is_eq(P.port(q), 0), h, path, top, depth, n, q)

# blend: kdemand.blend:429
def Demand.wk.q(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +q) = r
  Demand.wk.c(Demand.wk.down(4294967295n, Dn{Demand.dn.can(q, depth), h, path, top, depth, q}), n)

# blend: kdemand.blend:436
def Demand.demand.go(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          match st:
            case 0:
              Demand.demand.go(p, Demand.wk.q(P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st}

# blend: kdemand.blend:450
def Demand.demand(k: Nat, d: D) -> D:
  d.end(Demand.demand.go(k, d))

# blend: kdemand.blend:218
def DemandEv.Res() -> Type: P.H

# blend: kdemand.blend:461
def DemandEv.after(h: DemandEv.Res(), +x: N.Ext) -> DemandEv.Res():
  KN.ev.settle(h, x)

# blend: kdemand.blend:217
def DemandEv.S() -> Type: Unit

# blend: kdemand.blend:219
def DemandEv.note(u: DemandEv.S(), +x: U32, +y: U32) -> DemandEv.S():
  u

# blend: kdemand.blend:221
def DemandEv.fin(h: P.H, u: DemandEv.S()) -> DemandEv.Res():
  h

# blend: kdemand.blend:223
def DemandEv.wd(w: KN.Wd, u: DemandEv.S()) -> DemandEv.Res():
  KN.wd.h(w)

# blend: kdemand.blend:225
def DemandEv.erased(h: DemandEv.Res(), +x: N.Ext) -> DemandEv.Res():
  KN.ev.settle(h, x)

# blend: kdemand.blend:228
def DemandEv.wk.pop.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  d.go(h, path, p, (depth - 1 : U32), n)

# blend: kdemand.blend:232
def DemandEv.wk.pop(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      DemandEv.wk.pop.r(KM.m_get(path, depth), h, depth, n)

# blend: kdemand.blend:239
def DemandEv.wk.past(gone: Bool, h: P.H, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      DemandEv.wk.pop(h, path, depth, n)
    case False{}:
      d.go(h, path, p, depth, n)

# blend: kdemand.blend:246
def DemandEv.wk.hp(r: P.H & U32, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  (h, +hp) = r
  DemandEv.wk.past(U32.is_eq(hp, 0), h, path, p, depth, n)

# blend: kdemand.blend:256
def DemandEv.wk.back.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  DemandEv.wk.hp(P.rd(h, p), path, p, (depth - 1 : U32), n)

# blend: kdemand.blend:260
def DemandEv.wk.back(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      DemandEv.wk.back.r(KM.m_get(path, depth), h, depth, n)

# blend: kdemand.blend:267
def DemandEv.wk.hb.go(gone: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      DemandEv.wk.back(h, path, depth, (n + 1 : U32))
    case False{}:
      fw.scan(h, path, top, depth, n, 3)

# blend: kdemand.blend:274
def DemandEv.wk.hb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +hb) = r
  DemandEv.wk.hb.go(U32.is_eq(hb, 0), h, path, top, depth, n)

# blend: kchain.blend:25
def DemandEv.go.gen(+rn: U32, +t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite(~DemandEv.S(), ~DemandEv.Res(), ~DemandEv.note, ~DemandEv.fin, ~DemandEv.after, ~DemandEv.erased, P.rk(ha), rn, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# blend: kchain.blend:70
def DemandEv.go.id(+t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite_id(~DemandEv.S(), ~DemandEv.Res(), ~DemandEv.note, ~DemandEv.fin, ~DemandEv.after, ~DemandEv.erased, P.rk(ha), t, h, st, a, b, ha, hb, pa, pb, e0, e1, P.nil(), P.nil())

# blend: kchain.blend:39
def DemandEv.go.wd.w(+er: Bool, w: KN.Wd, st: DemandEv.S()) -> DemandEv.Res():
  match er w:
    case True{} KN.Wd{h, ns, +sx}:
      DemandEv.erased(DemandEv.wd(KN.Wd{h, ns, sx}, st), sx)
    case False{} KN.Wd{h, ns, +sx}:
      DemandEv.after(DemandEv.wd(KN.Wd{h, ns, sx}, st), sx)

# blend: kchain.blend:32
def DemandEv.rule_erases(r: Blend_1.Rule) -> Bool:
  match r:
    case Blend_1.RWire{xs, ls}:
      Blend_1.nv.any(xs)
    case Blend_1.RStuck{}:
      False{}

# blend: kchain.blend:48
def DemandEv.go.wd(r: Blend_1.Rule, w: KN.Wd, st: DemandEv.S()) -> DemandEv.Res():
  DemandEv.go.wd.w(DemandEv.rule_erases(r), w, st)

# blend: kchain.blend:79
def DemandEv.go.interp.id(+t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      DemandEv.go.wd(Blend_1.rule_id(KN.kof(ha), t), KN.apply_rule(Blend_1.rule_id(KN.kof(ha), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, N.Ext4{e0, e1, P.nil(), P.nil()}), st)

# blend: kchain.blend:51
def DemandEv.go.interp.pl(r: P.Pl, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> DemandEv.Res():
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      DemandEv.go.wd(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KN.apply_rule(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), h, a, b, ha, hb, pa, pb, N.Ext4{e0, e1, e2, e3}), st)

# blend: kchain.blend:59
def DemandEv.go.interp(ctl: Bool, +t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match ctl:
    case True{}:
      match x:
        case N.Ext4{+e0, +e1, +e2, +e3}:
          DemandEv.go.interp.pl(P.peel_ctl(KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case False{}:
      DemandEv.go.wd(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KN.apply_rule(Blend_1.rule(KN.kof(ha), KN.kof(hb), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, x), st)

# blend: kchain.blend:88
def DemandEv.go.loop(+id: Bool, +fast: Bool, +t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match id fast:
    case True{} True{}:
      DemandEv.go.id(t, h, st, a, b, ha, hb, pa, pb, x)
    case True{} False{}:
      DemandEv.go.interp.id(t, h, st, a, b, ha, hb, pa, pb, x)
    case False{} _:
      DemandEv.go.interp(U32.is_eq(P.rk(ha), 10) && U32.is_eq(P.rk(hb), 11), t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:99
def DemandEv.is_id(+x: N.Ext, +a: U32, +b: U32, +hb: U32) -> Bool:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      U32.is_eq(P.rk(hb), 1) && U32.is_eq(e2, (b + 2 : U32)) && U32.is_eq(e3, (b + 1 : U32)) && Bool.not(KN.own(e0, a, b) || KN.own(e1, a, b))

# blend: kchain.blend:104
def DemandEv.go.which(gen: Bool, +fast: Bool, +rn: U32, +t: Bool, h: P.H, st: DemandEv.S(), +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  match gen:
    case True{}:
      DemandEv.go.gen(rn, t, h, st, a, b, ha, hb, pa, pb, x)
    case False{}:
      DemandEv.go.loop(DemandEv.is_id(x, a, b, hb), fast, t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:113
def DemandEv.go.rule(r: P.H & Bool, st: DemandEv.S(), +fast: Bool, +rn: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> DemandEv.Res():
  (h, +t) = r
  DemandEv.go.which(fast && Bool.not(KN.any_partner(x, a, b)), fast, rn, t, h, st, a, b, ha, hb, pa, pb, x)

# blend: kchain.blend:117
def DemandEv.go.ext.r(+rn: U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: DemandEv.S()) -> DemandEv.Res():
  DemandEv.go.rule(KR.test(~DemandEv.S(), ~DemandEv.Res(), ~DemandEv.note, ~DemandEv.fin, ~DemandEv.after, ~DemandEv.erased, rn, h, ha, hb, KN.payload(ha, 0, a2), KN.payload(hb, b1, b2)), st, fast, rn, a, b, ha, hb, KN.payload(ha, 0, a2), KN.payload(hb, b1, b2),
    N.Ext4{KN.aux_or_nil(U32.is_lt(1, KN.arity(ha)), a1), KN.aux_or_nil(U32.is_lt(2, KN.arity(ha)), a2),
      KN.aux_or_nil(U32.is_lt(1, KN.arity(hb)), b1), KN.aux_or_nil(U32.is_lt(2, KN.arity(hb)), b2)})

# blend: kchain.blend:125
def DemandEv.go.ext(+fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H, st: DemandEv.S()) -> DemandEv.Res():
  DemandEv.go.ext.r(KR.rule_no(P.rk(ha), P.rk(hb)), fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

# blend: kchain.blend:128
def DemandEv.go.b2(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32) -> DemandEv.Res():
  (h, +b2) = r
  DemandEv.go.ext(fast, a, b, ha, hb, a1, a2, b1, b2, h, st)

# blend: kchain.blend:132
def DemandEv.go.b1(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32) -> DemandEv.Res():
  (h, +b1) = r
  DemandEv.go.b2(P.rd(h, (b + 3 : U32)), st, fast, a, b, ha, hb, a1, a2, b1)

# blend: kchain.blend:136
def DemandEv.go.a2(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32) -> DemandEv.Res():
  (h, +a2) = r
  DemandEv.go.b1(P.rd(h, (b + 2 : U32)), st, fast, a, b, ha, hb, a1, a2)

# blend: kchain.blend:140
def DemandEv.go.a1(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> DemandEv.Res():
  (h, +a1) = r
  DemandEv.go.a2(P.rd(h, (a + 3 : U32)), st, fast, a, b, ha, hb, a1)

# blend: kchain.blend:146
def DemandEv.go(h: P.H, st: DemandEv.S(), +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> DemandEv.Res():
  DemandEv.go.a1(P.rd(h, (a + 2 : U32)), st, fast, a, b, ha, hb)

# blend: kdemand.blend:284
def DemandEv.wk.rw(+sb: U32, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match sb:
    case 0:
      DemandEv.wk.back(DemandEv.go(h, Unit{}, True{}, a, b, ha, hb), path, depth, (n + 1 : U32))
    case 1:
      fw.scan(h, path, top, depth, n, 3)
    case _:
      DemandEv.wk.hb(P.rd(DemandEv.go(h, Unit{}, True{}, a, b, ha, hb), b), path, top, depth, n)

# blend: kdemand.blend:293
def DemandEv.nd.lz(z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match z:
    case P.Lz{h, +lazy, +k}:
      match lazy:
        case True{}:
          D{h, path, top, depth, n, 2}
        case False{}:
          DemandEv.wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:302
def DemandEv.nd.pb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  (h, +pb) = r
  DemandEv.nd.lz(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:306
def DemandEv.nd.go(chk: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match chk:
    case True{}:
      DemandEv.nd.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, a, b, ha, hb)
    case False{}:
      DemandEv.wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# blend: kdemand.blend:314
def DemandEv.may_need(+ha: U32, +hb: U32) -> Bool:
  (U32.is_eq(P.rk(ha), 2) || U32.is_eq(P.rk(ha), 9)) && U32.is_eq(P.rk(hb), 5) && U32.is_eq(P.form(hb), 0)

# blend: kdemand.blend:320
def DemandEv.wk.ori(neg: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +x: U32, +y: U32, +hx: U32, +hy: U32) -> D:
  match neg:
    case True{}:
      DemandEv.nd.go(DemandEv.may_need(hx, hy), h, path, top, depth, n, x, y, hx, hy)
    case False{}:
      fw.scan(h, path, top, depth, n, 7)

# blend: kdemand.blend:327
def DemandEv.wk.hy(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32, +hx: U32) -> D:
  (h, +hy) = r
  DemandEv.wk.ori(KR.kind_neg(P.rk(hx)), h, path, top, depth, n, top, y, hx, hy)

# blend: kdemand.blend:331
def DemandEv.wk.hx(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hx) = r
  DemandEv.wk.hy(P.rd(h, y), path, top, depth, n, y, hx)

# blend: kdemand.blend:339
def DemandEv.wk.root.v(+void: Bool, h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match void:
    case True{}:
      d.stop(h, path, 0, depth, n, 8)
    case False{}:
      d.stop(h, path, 0, depth, n, 1)

# blend: kchain.blend:251
def DemandEv.static_meet(h: P.H, st: DemandEv.S()) -> DemandEv.Res():
  DemandEv.fin(h, st)

# blend: kchain.blend:174
def DemandEv.se.put.go(+skip: Bool, h: P.H, +e: U32, +s: U32) -> P.H:
  match skip:
    case True{}:
      h
    case False{}:
      P.wr(h, (e + 1 : U32), s)

# blend: kchain.blend:182
def DemandEv.se.put(h: P.H, +e: U32, +s: U32, +x: U32) -> P.H:
  DemandEv.se.put.go(P.is_static(e) || U32.is_eq(P.base(e), x), h, e, s)

# blend: kchain.blend:192
def DemandEv.se.note(+none: Bool, st: DemandEv.S(), +e: U32, +s: U32) -> DemandEv.S():
  match none:
    case True{}:
      st
    case False{}:
      DemandEv.note(st, e, s)

# blend: kchain.blend:203
def DemandEv.se.notes(+loop: Bool, st: DemandEv.S(), +k: U32, +e1: U32, +e2: U32) -> DemandEv.S():
  match loop:
    case True{}:
      DemandEv.note(st, P.era(), P.era())
    case False{}:
      DemandEv.se.note(U32.is_lt(KR.kind_arity(k), 3), DemandEv.se.note(U32.is_lt(KR.kind_arity(k), 2), st, e1, P.era()), e2, P.era())

# blend: kchain.blend:210
def DemandEv.se.do(h: P.H, st: DemandEv.S(), +x: U32, +k: U32, +e1: U32, +e2: U32) -> DemandEv.Res():
  DemandEv.erased(DemandEv.fin(DemandEv.se.put(DemandEv.se.put(h, e1, P.era(), x), e2, P.era(), x),
      DemandEv.se.notes(Bool.not(P.is_static(e1)) && U32.is_eq(P.base(e1), x), st, k, e1, e2)),
    N.Ext4{e1, e2, P.nil(), P.nil()})

# blend: kchain.blend:185
def DemandEv.se.free(+data: Bool, h: P.H, +x: U32, +hx: U32, +w2: U32, +w3: U32) -> P.H:
  match data:
    case True{}:
      P.free(P.drop(h, P.form(hx), KN.payload(hx, w2, w3)), x)
    case False{}:
      P.free(h, x)

# blend: kchain.blend:224
def DemandEv.se.go(+ok: Bool, +stuck: Bool, h: P.H, st: DemandEv.S(), +x: U32, +hx: U32, +k: U32, +w2: U32, +w3: U32) -> DemandEv.Res():
  match ok stuck:
    case True{} False{}:
      DemandEv.se.do(DemandEv.se.free(KR.is_data(P.rk(hx)), h, x, hx, w2, w3), st, x, k,
        KN.aux_or_nil(U32.is_lt(1, KR.kind_arity(k)), w2), KN.aux_or_nil(U32.is_lt(2, KR.kind_arity(k)), w3))
    case True{} True{}:
      DemandEv.fin(h, st)
    case False{} _:
      DemandEv.fin(P.h_err(h), st)

# blend: kchain.blend:217
def DemandEv.se.stuck(+neg: Bool, +k: U32) -> U32:
  match neg:
    case True{}:
      KR.stuck_by(k, 7)
    case False{}:
      KR.stuck_by(6, k)

# blend: kchain.blend:234
def DemandEv.se.k(+k: U32, h: P.H, st: DemandEv.S(), +x: U32, +s: U32, +hx: U32, +w2: U32, +w3: U32) -> DemandEv.Res():
  DemandEv.se.go(U32.is_eq(s, P.era()), U32.is_ne(DemandEv.se.stuck(KR.kind_neg(k), k), 0), h, st, x, hx, k, w2, w3)

# blend: kchain.blend:237
def DemandEv.se.w3(r: P.H & U32, st: DemandEv.S(), +x: U32, +s: U32, +hx: U32, +w2: U32) -> DemandEv.Res():
  (h, +w3) = r
  DemandEv.se.k(P.rk(hx), h, st, x, s, hx, w2, w3)

# blend: kchain.blend:241
def DemandEv.se.w2(r: P.H & U32, st: DemandEv.S(), +x: U32, +s: U32, +hx: U32) -> DemandEv.Res():
  (h, +w2) = r
  DemandEv.se.w3(P.rd(h, (x + 3 : U32)), st, x, s, hx, w2)

# blend: kchain.blend:245
def DemandEv.se.hx(r: P.H & U32, st: DemandEv.S(), +x: U32, +s: U32) -> DemandEv.Res():
  (h, +hx) = r
  DemandEv.se.w2(P.rd(h, (x + 2 : U32)), st, x, s, hx)

# blend: kchain.blend:256
def DemandEv.static_erase(h: P.H, st: DemandEv.S(), +x: U32, +s: U32) -> DemandEv.Res():
  DemandEv.se.hx(P.rd(h, x), st, x, s)

# blend: kchain.blend:259
def DemandEv.int.st(+sx: Bool, h: P.H, st: DemandEv.S(), +x: U32, +y: U32) -> DemandEv.Res():
  match sx:
    case True{}:
      DemandEv.static_meet(h, st)
    case False{}:
      DemandEv.static_erase(h, st, x, y)

# blend: kchain.blend:149
def DemandEv.ori(neg: Bool, h: P.H, st: DemandEv.S(), +fast: Bool, +x: U32, +y: U32, +hx: U32, +hy: U32) -> DemandEv.Res():
  match neg:
    case True{}:
      DemandEv.go(h, st, fast, x, y, hx, hy)
    case False{}:
      DemandEv.go(h, st, fast, y, x, hy, hx)

# blend: kchain.blend:156
def DemandEv.int.y(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +x: U32, +y: U32, +hx: U32) -> DemandEv.Res():
  (h, +hy) = r
  DemandEv.ori(KR.kind_neg(P.rk(hx)), h, st, fast, x, y, hx, hy)

# blend: kchain.blend:160
def DemandEv.int.x(r: P.H & U32, st: DemandEv.S(), +fast: Bool, +x: U32, +y: U32) -> DemandEv.Res():
  (h, +hx) = r
  DemandEv.int.y(P.rd(h, y), st, fast, x, y, hx)

# blend: kchain.blend:266
def DemandEv.int.s(+sy: Bool, h: P.H, st: DemandEv.S(), +fast: Bool, +x: U32, +y: U32) -> DemandEv.Res():
  match sy:
    case True{}:
      DemandEv.int.st(P.is_static(x), h, st, x, y)
    case False{}:
      DemandEv.int.x(P.rd(h, x), st, fast, x, y)

# blend: kchain.blend:277
def DemandEv.interact.f(h: P.H, st: DemandEv.S(), +fast: Bool, +x: U32, +y: U32) -> DemandEv.Res():
  DemandEv.int.s(U32.is_eq(((x .|. y : U32) .&. 3 : U32), 3), h, st, fast, x, y)

# blend: kdemand.blend:346
def DemandEv.wk.root.go(c: Bool, +void: Bool, h: P.H, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  match c:
    case True{}:
      d.go(DemandEv.interact.f(h, Unit{}, True{}, P.iface(), y), path, P.iface(), depth, (n + 1 : U32))
    case False{}:
      DemandEv.wk.root.v(void, h, path, depth, n)

# blend: kdemand.blend:353
def DemandEv.wk.root(r: P.H & U32, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hy) = r
  DemandEv.wk.root.go(U32.is_eq(P.rk(hy), 11), U32.is_eq(P.rk(hy), 7), h, path, depth, n, y)

# blend: kdemand.blend:357
def DemandEv.wk.pair(root: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  match root:
    case True{}:
      DemandEv.wk.root(P.rd(h, y), path, depth, n, y)
    case False{}:
      DemandEv.wk.hx(P.rd(h, top), path, top, depth, n, y)

# blend: kdemand.blend:368
def DemandEv.wk.sn(+neg: Bool, +stuck: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match neg stuck:
    case True{} False{}:
      DemandEv.wk.back(DemandEv.static_erase(h, Unit{}, top, q), path, depth, (n + 1 : U32))
    case True{} True{}:
      fw.scan(h, path, top, depth, n, 3)
    case False{} _:
      fw.scan(h, path, top, depth, n, 7)

# blend: kdemand.blend:377
def DemandEv.wk.sx(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  (h, +hx) = r
  DemandEv.wk.sn(KR.kind_neg(P.rk(hx)), U32.is_ne(KN.se.stuck(KR.kind_neg(P.rk(hx)), P.rk(hx)), 0), h, path, top, depth, n, q)

# blend: kdemand.blend:382
def DemandEv.wk.sr(+root: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match root:
    case True{}:
      DemandEv.wk.root.v(U32.is_eq(q, P.era()), h, path, depth, n)
    case False{}:
      DemandEv.wk.sx(P.rd(h, top), path, top, depth, n, q)

# blend: kdemand.blend:389
def DemandEv.wk.q.go(st: Bool, +pr: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match st pr:
    case True{} _:
      DemandEv.wk.sr(U32.is_eq(top, P.iface()), h, path, top, depth, n, q)
    case False{} True{}:
      DemandEv.wk.pair(U32.is_eq(top, P.iface()), h, path, top, depth, n, q)
    case False{} False{}:
      wk.push(U32.is_eq(((depth + 1 : U32) .&. depth : U32), 0), h, path, top, depth, n, P.base(q))

# blend: kdemand.blend:400
def DemandEv.dn.can(+q: U32, +depth: U32) -> Bool:
  Bool.not(P.pri(q)) && U32.is_ne(((depth + 1 : U32) .&. depth : U32), 0)

# blend: kdemand.blend:403
def DemandEv.dn.r(r: P.H & U32, path: KM.M, +x: U32, +depth: U32) -> Dn:
  (h, +q) = r
  Dn{DemandEv.dn.can(q, depth), h, path, x, depth, q}

# blend: kdemand.blend:407
def DemandEv.dn.step(h: P.H, path: KM.M, +top: U32, +depth: U32, +q: U32) -> Dn:
  DemandEv.dn.r(P.rd(h, (P.base(q) + 1 : U32)), KM.m_set(path, (depth + 1 : U32), top), P.base(q), (depth + 1 : U32))

# blend: kdemand.blend:410
def DemandEv.wk.down(f: Nat, s: Dn) -> Dn:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case Dn{+more, h, path, +top, +depth, +q}:
          match more:
            case True{}:
              DemandEv.wk.down(g, DemandEv.dn.step(h, path, top, depth, q))
            case False{}:
              Dn{False{}, h, path, top, depth, q}

# blend: kdemand.blend:423
def DemandEv.wk.c(s: Dn, +n: U32) -> D:
  match s:
    case Dn{+more, h, path, +top, +depth, +q}:
      DemandEv.wk.q.go(P.is_static(q), U32.is_eq(P.port(q), 0), h, path, top, depth, n, q)

# blend: kdemand.blend:429
def DemandEv.wk.q(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +q) = r
  DemandEv.wk.c(DemandEv.wk.down(4294967295n, Dn{DemandEv.dn.can(q, depth), h, path, top, depth, q}), n)

# blend: kdemand.blend:436
def DemandEv.demand.go(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          match st:
            case 0:
              DemandEv.demand.go(p, DemandEv.wk.q(P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st}

# blend: kdemand.blend:450
def DemandEv.demand(k: Nat, d: D) -> D:
  d.end(DemandEv.demand.go(k, d))
