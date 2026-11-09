import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ../spike/kprim.bend as P
import ../spike/knet.bend as KN
import ../spike/kstrat.bend as KS
import ../spike/kmem_grow.bend as KM
import ../spike/kdemand.bend as KD

# Splicing (Cells, re-scoped by the bridge: `bridge-recursion`): a
# template, a top-level function the lowering made closed, copied into a
# running net where demand stopped needing it (state 2). Demand stops with
# its top the application whose principal port faces the data node that
# holds the template's handle (kstrat.bend's d.at); the copy's root, a
# function bind, takes that node's slot, so the application faces the
# bind and demand walks on from where it stopped. Every other node is made
# fresh, its template index mapped to its reference; erasers are made
# static as the loader makes them (KN.load). A template is lowered at depth
# 0, so every level in the copy is raised by the application's level,
# where it is applied (the Cells plan's item 2, an experiment); a level
# past the header's field is an error, as at load. A handle met by an
# operator, which carries no level, is spliced unraised: the operator
# meeting a bind stays stuck.

# Where the copy goes
# ===================

# the net, and the reference each template node got
type Sp is Type:
  Sp{h: P.H, map: Array<U32>}

def sp.place(+fresh: Bool, h: P.H, +r: U32, +hd: U32, +w: U32) -> P.H & U32:
  match fresh:
    case True{}:
      P.node(h, hd, w)
    case False{}:
      P.renode(h, r, hd, w)

def sp.new_pw(q: P.H & P.PW, +k: U32) -> P.H & U32:
  (h, pw) = q
  P.node_pw(h, k, pw)

def sp.renew_pw(q: P.H & P.PW, +r: U32, +k: U32) -> P.H & U32:
  (h, pw) = q
  P.renode_pw(h, r, k, pw)

def sp.place_pw(+fresh: Bool, q: P.H & P.PW, +r: U32, +k: U32) -> P.H & U32:
  match fresh:
    case True{}:
      sp.new_pw(q, k)
    case False{}:
      sp.renew_pw(q, r, k)

# a level raised by `by`, a fan's site left as it is
def sp.raise(+none: Bool, +l: U32, +by: U32) -> U32:
  match none:
    case True{}:
      l
    case False{}:
      (l + by : U32)

def sp.fan(+fresh: Bool, h: P.H, +r: U32, +k: U32, +site: U32, +l: U32) -> P.H & U32:
  sp.place(fresh, P.err_if(KN.fan_too_big(U32.is_eq(l, V.nolvl()), site, l), h), r, KN.fan_hd(k, site, l), 0)

# template node t, fresh or in slot r, its levels raised by `by`
def sp.node(+fresh: Bool, h: P.H, +r: U32, t: T.TNode, +by: U32) -> P.H & U32:
  match t:
    case T.TF{k, +site, +lvl}:
      sp.fan(fresh, h, r, N.kcode(k), site, sp.raise(U32.is_eq(lvl, V.nolvl()), lvl, by))
    case T.TN{k, p}:
      match p:
        case V.PVal{v}:
          sp.place_pw(fresh, P.put(h, v), r, N.kcode(k))
        case V.PLvl{+l}:
          sp.place(fresh, P.err_if(KN.too_big((l + by : U32)), h), r, P.hd(N.kcode(k), (l + by : U32)), 0)
        case V.PLift{+i, +up, +amt}:
          sp.place(fresh, P.err_if(KN.too_big((i + by : U32)) || U32.is_ge(amt, 2147483648), h), r,
            P.hd(N.kcode(k), (i + by : U32)), KN.lift_word(up, amt))
        case _:
          sp.place(fresh, h, r, KN.bare_hd(N.kcode(k)), 0)

def sp.put(q: P.H & U32, map: Array<U32>, +i: U32) -> Sp:
  (h, +ref) = q
  Sp{h, Array.set(U32, map, i, ref)}

# template node i: the root, rn, in the leaf's slot, the others fresh
def sp.node_at(s: Sp, t: T.TNode, +i: U32, +rn: U32, +leaf: U32, +by: U32) -> Sp:
  match s:
    case Sp{h, map}:
      sp.put(sp.node(Bool.not(U32.is_eq(i, rn)), h, leaf, t, by), map, i)

def sp.nodes(ts: List<&2, T.TNode>, +i: U32, s: Sp, +rn: U32, +leaf: U32, +by: U32) -> Sp:
  match ts:
    case Nil{}:
      s
    case Con{t, rest}:
      sp.nodes(rest, (i + 1 : U32), sp.node_at(s, t, i, rn, leaf, by), rn, leaf, by)

# Links and statics
# =================

def sp.ref(q: Array<U32> & U32, +p: U32) -> Array<U32> & U32:
  (map, +b) = q
  (map, (b + p : U32))

def sp.end(map: Array<U32>, e: T.TEnd) -> Array<U32> & U32:
  match e:
    case T.TE{+n, +p}:
      sp.ref(Array.get(U32, map, n), p)

def sp.link2(q: Array<U32> & U32, +x: U32, h: P.H) -> Sp:
  (map, +y) = q
  Sp{P.link(h, x, y), map}

def sp.link1(q: Array<U32> & U32, b: T.TEnd, h: P.H) -> Sp:
  (map, +x) = q
  sp.link2(sp.end(map, b), x, h)

def sp.link(s: Sp, l: T.TLink) -> Sp:
  match s:
    case Sp{h, map}:
      match l:
        case T.TL{a, b}:
          sp.link1(sp.end(map, a), b, h)

def sp.links(ls: List<&2, T.TLink>, s: Sp) -> Sp:
  match ls:
    case Nil{}:
      s
    case Con{l, rest}:
      sp.links(rest, sp.link(s, l))

def sp.static(q: Array<U32> & U32, h: P.H) -> Sp:
  (map, +x) = q
  Sp{KN.ld.hd(P.rd(h, x), x), map}

# the template's k nodes from index i, each eraser made static
def sp.statics(k: Nat, s: Sp, +i: U32) -> Sp:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sp{h, map}:
          sp.statics(p, sp.static(Array.get(U32, map, i), h), (i + 1 : U32))

# The splice
# ==========

def sp.walk(s: Sp, path: KM.M, +top: U32, +depth: U32, +n: U32) -> KD.D:
  match s:
    case Sp{h, map}:
      KD.d.go(h, path, top, depth, n)

# the application's level, the amount the copy is raised: none for an
# operator, which has no level
def sp.by.k(+ap: Bool, +hd: U32) -> U32:
  match ap:
    case True{}:
      P.fld(hd)
    case False{}:
      0

def sp.by(+hd: U32) -> U32:
  sp.by.k(U32.is_eq(P.rk(hd), N.kcode(R.KAp{})), hd)

def sp.copy(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, +by: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  sp.walk(sp.statics(U32.to_nat(size), sp.links(links, sp.nodes(nodes, 0, Sp{h, [0 : U32^T.depth_for(31n, size, 0n)]}, rn, leaf, by)), 0),
    path, top, depth, n)

def sp.top(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  (h, +hd) = q
  sp.copy(h, path, top, depth, n, leaf, sp.by(hd), nodes, links, rn, size)

def sp.word(q: P.H & U32, +hb: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  (h, +w) = q
  sp.top(P.rd(P.drop(h, P.form(hb), w), top), path, top, depth, n, leaf, nodes, links, rn, size)

def sp.hb(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  (h, +hb) = q
  sp.word(P.rd(h, (leaf + 2 : U32)), hb, path, top, depth, n, leaf, nodes, links, rn, size)

def sp.leaf(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  (h, +leaf) = q
  sp.hb(P.rd(h, leaf), path, top, depth, n, leaf, nodes, links, rn, size)

# the root's end must be a node's principal port, as a function's bind is;
# any other root is an error, the copy not made and demand stopped stuck
# (state 3), lest it meet the same need again
def sp.root(+ok: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +rn: U32, +size: U32) -> KD.D:
  match ok:
    case True{}:
      sp.leaf(KS.d.at(h, top), path, top, depth, n, nodes, links, rn, size)
    case False{}:
      KD.D{P.err_if(True{}, h), path, top, depth, n, 3}

# t spliced where d waits, d stopped needing t's handle (state 2)
def splice(d: KD.D, t: T.Tpl) -> KD.D:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match t:
        case T.Tpl{nodes, links, root, +size}:
          match root:
            case T.TE{+rn, +rp}:
              sp.root(U32.is_eq(rp, 0), h, path, top, depth, n, nodes, links, rn, size)
