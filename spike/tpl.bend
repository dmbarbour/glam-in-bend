import Base
import ./val.bend as V
import ./store.bend as S
import ./rules.bend as R
import ./net.bend as N

# Templates: closed nets as plain data, instantiated into the store. A
# template's fans name their lowering site; each instantiation supplies
# one fresh instance number for all of them (Design.md, "Interaction
# Nets": lowered templates use local fan sites).

type TNode is Data:
  TN{k: R.NodeKind, p: V.Pay}
  TF{k: R.NodeKind, +site: U32, +lvl: U32}

type TEnd is Data:
  TE{+n: U32, +port: U32}

type TLink is Data:
  TL{a: TEnd, b: TEnd}

# nodes, links, the exposed port (positive), and how many nodes
type Tpl is Data:
  Tpl{nodes: List<&2, TNode>, links: List<&2, TLink>, root: TEnd, +size: U32}

# Instantiation
# =============

type Inst is Type:
  Inst{q: N.Q, map: Array<U32>, +inst: U32}

def pick_nat(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# the least d, up to f more, with 2^d >= n
def depth_for(f: Nat, +n: U32, +d: Nat) -> Nat:
  match f:
    case 0n:
      d
    case 1n+p:
      pick_nat(U32.is_le(n, U32.from_nat(Nat.pow(2n, d))), d, depth_for(p, n, 1n+d))

def tnode_pay(t: TNode, +inst: U32) -> V.Pay:
  match t:
    case TN{k, p}:
      p
    case TF{k, +site, +lvl}:
      V.PFan{V.fan_new(site, inst, lvl)}

def tnode_kind(t: TNode) -> R.NodeKind:
  match t:
    case TN{k, p}:
      k
    case TF{k, s, l}:
      k

def inst.put(r: N.Q & U32, map: Array<U32>, +i: U32, +inst: U32) -> Inst:
  (q, +ref) = r
  Inst{q, Array.set(U32, map, i, ref), inst}

def inst.node(s: Inst, +t: TNode, +i: U32) -> Inst:
  match s:
    case Inst{q, map, +inst}:
      inst.put(N.node(q, tnode_kind(t), tnode_pay(t, inst)), map, i, inst)

def inst.nodes(ts: List<&2, TNode>, +i: U32, s: Inst) -> Inst:
  match ts:
    case Nil{}:
      s
    case Con{+t, rest}:
      inst.nodes(rest, (i + 1 : U32), inst.node(s, t, i))

def inst.ref(r: Array<U32> & U32, +port: U32) -> Array<U32> & U32:
  (map, +x) = r
  (map, S.ref_at(x, port))

def inst.end(map: Array<U32>, e: TEnd) -> Array<U32> & U32:
  match e:
    case TE{+n, +port}:
      inst.ref(Array.get(U32, map, n), port)

def inst.link2(r: Array<U32> & U32, +x: U32, q: N.Q, +inst: U32) -> Inst:
  (map, +y) = r
  Inst{N.link(q, x, y), map, inst}

def inst.link1(r: Array<U32> & U32, b: TEnd, q: N.Q, +inst: U32) -> Inst:
  (map, +x) = r
  inst.link2(inst.end(map, b), x, q, inst)

def inst.link(s: Inst, l: TLink) -> Inst:
  match s:
    case Inst{q, map, +inst}:
      match l:
        case TL{a, b}:
          inst.link1(inst.end(map, a), b, q, inst)

def inst.links(ls: List<&2, TLink>, s: Inst) -> Inst:
  match ls:
    case Nil{}:
      s
    case Con{l, rest}:
      inst.links(rest, inst.link(s, l))

def inst.root(r: Array<U32> & U32, q: N.Q) -> N.Q & U32:
  (map, +x) = r
  (q, x)

def inst.done(s: Inst, root: TEnd) -> N.Q & U32:
  match s:
    case Inst{q, map, inst}:
      inst.root(inst.end(map, root), q)

# put a copy of t in the store: the reference of its exposed port
def instantiate(q: N.Q, t: Tpl, +inst: U32) -> N.Q & U32:
  match t:
    case Tpl{nodes, links, root, +size}:
      inst.done(inst.links(links, inst.nodes(nodes, 0, Inst{q, [0 : U32^depth_for(31n, size, 0n)], inst})), root)

# Running a net
# =============

# link a root to the net's exposed port, then reduce
def e_q(e: N.E) -> N.Q:
  match e:
    case N.E{q, m}:
      q

def run.root(r: N.Q & U32, +x: U32, +fuel: Nat) -> N.Q & U32:
  (q, +root) = r
  (e_q(N.eval(64n, fuel, N.E{N.link(q, root, x), True{}})), root)

def run.go(r: N.Q & U32, +fuel: Nat) -> N.Q & U32:
  (q, +x) = r
  run.root(N.node(q, R.KRoot{}, V.PNone{}), x, fuel)

def run(t: Tpl, +fuel: Nat) -> N.Q & U32:
  run.go(instantiate(N.q_new(), t, 1), fuel)

# what reached the root: its value, if the root's peer is data
def result.val(isdata: Bool, p: V.Pay) -> Maybe<&2, V.Val>:
  match isdata:
    case True{}:
      match p:
        case V.PVal{v}:
          Some{v}
        case _:
          None{}
    case False{}:
      None{}

def result.pay(r: N.Q & V.Pay, +isdata: Bool) -> N.Q & Maybe<&2, V.Val>:
  (q, p) = r
  (q, result.val(isdata, p))

def result.hdr(r: N.Q & U32, +peer: U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +h) = r
  result.pay(N.q_pay(q, peer), U32.is_eq((h .&. 15 : U32), 5))

def result.peer(r: N.Q & U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +peer) = r
  result.hdr(N.q_word(q, peer, 0), peer)

def result(r: N.Q & U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +root) = r
  result.peer(N.q_word(q, root, 1))
