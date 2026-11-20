import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ../spike/kprim.bend as P

# The splice's copy (glam/splice.bend): a template's nodes made fresh,
# its template indices mapped to their references, then its links made,
# the two passes the splice's laws are about (glam/SPLICE_LAWS.bend). An
# eraser makes no node: its index maps to the static, which its link
# writes in its peer's link word (cells-freeze.nested.host.splice.single).
# A module of its own, importing the primitives and not the kernel, so
# that the laws over the passes check without it (the Cells plan's
# .host.witness.verdicts: the splice's verdict was its imports').

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

def sp.fan(+fresh: Bool, h: P.H, +r: U32, +k: U32, +site: U32, +l: U32) -> P.H & U32:
  sp.place(fresh, P.err_if(P.fan_too_big(U32.is_eq(l, V.nolvl()), site, l), h), r, P.fan_hd(k, site, l), 0)

# a node of kind k with payload p, already raised
def sp.tn(+fresh: Bool, h: P.H, +r: U32, k: R.NodeKind, p: V.Pay) -> P.H & U32:
  match p:
    case V.PVal{v}:
      sp.place_pw(fresh, P.put(h, v), r, N.kcode(k))
    case V.PLvl{+l}:
      sp.place(fresh, P.err_if(P.too_big(l), h), r, P.hd(N.kcode(k), l), 0)
    case V.PLift{+i, +up, +amt}:
      sp.place(fresh, P.err_if(P.too_big(i) || U32.is_ge(amt, 2147483648), h), r,
        P.hd(N.kcode(k), i), P.lift_word(up, amt))
    case _:
      sp.place(fresh, h, r, P.bare_hd(N.kcode(k)), 0)

# template node t, fresh or in slot r, its levels raised by `by`, as
# val.bend raises them (V.raise_lvl, V.raise_pay; the laws raise_*)
def sp.node(+fresh: Bool, h: P.H, +r: U32, t: T.TNode, +by: U32) -> P.H & U32:
  match t:
    case T.TF{k, +site, +lvl}:
      sp.fan(fresh, h, r, N.kcode(k), site, V.raise_lvl(by, lvl))
    case T.TN{k, p}:
      sp.tn(fresh, h, r, k, V.raise_pay(by, p))

def sp.put(q: P.H & U32, map: Array<U32>, +i: U32) -> Sp:
  (h, +ref) = q
  Sp{h, Array.set(U32, map, i, ref)}

# an eraser of the template, kind 6 or 7, as tpl.made counts it
def sp.is_era(+t: T.TNode) -> Bool:
  match t:
    case T.TN{k, p}:
      U32.is_eq((N.kcode(k) .|. 1 : U32), 7)
    case T.TF{k, +site, +lvl}:
      False{}

# an eraser makes no node: its index holds the static in the map, so that
# a link to it writes the static in its peer's link word (the splice in
# one pass for statics, cells-freeze.nested.host.splice.single); an
# eraser linked to an eraser writes nothing, a pair demand never reaches
def sp.node_k(+era: Bool, s: Sp, +t: T.TNode, +i: U32, +by: U32) -> Sp:
  match era:
    case True{}:
      match s:
        case Sp{h, map}:
          Sp{h, Array.set(U32, map, i, P.era())}
    case False{}:
      match s:
        case Sp{h, map}:
          sp.put(sp.node(True{}, h, 0, t, by), map, i)

def sp.node_at(s: Sp, +t: T.TNode, +i: U32, +by: U32) -> Sp:
  sp.node_k(sp.is_era(t), s, t, i, by)

def sp.nodes(ts: List<&2, T.TNode>, +i: U32, s: Sp, +by: U32) -> Sp:
  match ts:
    case Nil{}:
      s
    case Con{t, rest}:
      sp.nodes(rest, (i + 1 : U32), sp.node_at(s, t, i, by), by)

# Links
# =====

def sp.ref(q: Array<U32> & U32, +p: U32) -> Array<U32> & U32:
  (map, +b) = q
  (map, (b + p : U32))

def sp.end(map: Array<U32>, e: T.TEnd) -> Array<U32> & U32:
  match e:
    case T.TE{+n, +p}:
      sp.ref(Array.get(U32, map, n), p)

def sp.link2(q: Array<U32> & U32, +x: U32, h: P.H) -> Sp:
  (map, +y) = q
  Sp{P.link_xx(h, x, y), map}

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
