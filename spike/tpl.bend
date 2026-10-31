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

def pick_u32(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

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

# The queue a run starts from: the active pairs found by walking the
# store in node order, each from its lower node, the last found first
# out, as the kernel's eager strategy builds its stack (kstrat.bend); the
# pairs the loader's links queued are dropped
type Seed is Type:
  Seed{q: N.Q, rq: List<&2, N.Redex>}

def seed.push(c: Bool, rq: List<&2, N.Redex>, +a: U32, +b: U32) -> List<&2, N.Redex>:
  match c:
    case True{}:
      N.Redex{a, b} <> rq
    case False{}:
      rq

def seed.peer(rr: N.Q & U32, rq: List<&2, N.Redex>, +ref: U32) -> Seed:
  (q, +p) = rr
  Seed{q, seed.push(U32.is_eq(S.ref_port(p), 0) && U32.is_gt(p, ref), rq, ref, p)}

def seed.live(live: Bool, q: N.Q, rq: List<&2, N.Redex>, +ref: U32) -> Seed:
  match live:
    case True{}:
      seed.peer(N.q_word(q, ref, 1), rq, ref)
    case False{}:
      Seed{q, rq}

def seed.hit(rr: N.Q & U32, rq: List<&2, N.Redex>, +ref: U32) -> Seed:
  (q, +h) = rr
  seed.live(U32.is_ne((h .&. 255 : U32), 0), q, rq, ref)

def seed.slots(n: Nat, +page: U32, +slot: U32, s: Seed) -> Seed:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case Seed{q, rq}:
          seed.slots(p, page, (slot + 1 : U32), seed.hit(N.q_word(q, S.mk_ref(page, slot, 0), 0), rq, S.mk_ref(page, slot, 0)))

def seed.pages(n: Nat, +page: U32, s: Seed) -> Seed:
  match n:
    case 0n:
      s
    case 1n+p:
      seed.pages(p, (page + 1 : U32), seed.slots(S.cap(), page, 0, s))

def seed.done(s: Seed, +itrs: U32, +errs: U32, +ser: U32) -> N.Q:
  match s:
    case Seed{q, rq}:
      match q:
        case N.Q{st, old, +i, +e, +r}:
          N.Q{st, rq, i, e, r}

def seed.start(r: S.Store & U32, +itrs: U32, +errs: U32, +ser: U32) -> N.Q:
  (st, +np) = r
  seed.done(seed.pages(U32.to_nat(np), 0, Seed{N.Q{st, Nil{}, itrs, errs, ser}, Nil{}}), itrs, errs, ser)

def seed(q: N.Q) -> N.Q:
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      seed.start(S.st_pages(st), itrs, errs, ser)

# link a root to the net's exposed port, then reduce from the pairs a
# walk finds
def e_q(e: N.E) -> N.Q:
  match e:
    case N.E{q, m}:
      q

def run.root(r: N.Q & U32, +x: U32, +fuel: Nat) -> N.Q & U32:
  (q, +root) = r
  (e_q(N.eval(64n, fuel, N.E{seed(N.link(q, root, x)), True{}})), root)

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
  result.pay(N.q_pay(q, peer), U32.is_eq((h .&. 255 : U32), 5))

def result.peer(r: N.Q & U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +peer) = r
  result.hdr(N.q_word(q, peer, 0), peer)

# finding the root: the first live Root node in the store
type Find is Type:
  Find{q: N.Q, +at: U32}

def find.hit(rr: N.Q & U32, +ref: U32, +at: U32) -> Find:
  (q, +h) = rr
  Find{q, pick_u32(U32.is_eq(at, S.nil()) && U32.is_eq((h .&. 255 : U32), 8), ref, at)}

def find.slots(n: Nat, +page: U32, +slot: U32, f: Find) -> Find:
  match n:
    case 0n:
      f
    case 1n+p:
      match f:
        case Find{q, +at}:
          find.slots(p, page, (slot + 1 : U32), find.hit(N.q_word(q, S.mk_ref(page, slot, 0), 0), S.mk_ref(page, slot, 0), at))

def find.pages(n: Nat, +page: U32, f: Find) -> Find:
  match n:
    case 0n:
      f
    case 1n+p:
      find.pages(p, (page + 1 : U32), find.slots(S.cap(), page, 0, f))

def find.start(r: S.Store & U32, rq: List<&2, N.Redex>, +itrs: U32, +errs: U32, +ser: U32) -> Find:
  (st, +np) = r
  find.pages(U32.to_nat(np), 0, Find{N.Q{st, rq, itrs, errs, ser}, S.nil()})

def find.done(f: Find) -> N.Q & U32:
  match f:
    case Find{q, +at}:
      (q, at)

def find_root(q: N.Q) -> N.Q & U32:
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      find.done(find.start(S.st_pages(st), rq, itrs, errs, ser))

def result.go(r: N.Q & U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +root) = r
  result.peer(N.q_word(q, root, 1))

# what reached the root, which a control may have moved (R.rule.root)
def result(r: N.Q & U32) -> N.Q & Maybe<&2, V.Val>:
  (q, +root) = r
  result.go(find_root(q))
