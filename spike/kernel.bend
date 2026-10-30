import Base
import ./val.bend as V
import ./tpl.bend as T
import ./nets.bend as X
import ./kprim.bend as P
import ./knet.bend as KN
import ./kstrat.bend as KS
import ./kmem_grow.bend as KM

# The kernel as a program, and the entry points tests use: a template
# reduced fully by the eager strategy or on demand (kstrat.bend), over the
# net of knet.bend.
#
#   kernel <k> [succ|ref|plus|plusref|lvl|lvlref|fma|fmaref|kpow|knum|komega|whnf] [lazy|profile|two|ev|evlazy|evtwo|evprofile]
#       reduce `k 2 succ 0` (2^k) built without levels; with plus
#       `k 2 (plus 1) 0`, adding by a partial application in a node; with
#       fma `k 2 (fma 1 1) 0`, by one in the data table; with lvl
#       `k 2 succ 0` with levels, as terms.py lowers it (k >= 2); kpow
#       `K 0 (k 2 succ 0)`; knum `K 0 #k`; komega `K 0 ((\z. z z) (\z. z
#       z))`; whnf `#k succ`, a function. Report value, counts, time; with
#       ref, by the interpreted table alone; with lazy, on demand (see
#       kstrat.bend's Demand), the state it ends in and the nodes left;
#       with profile, by the profiling strategy (kstrat.bend's Profiling),
#       the logical interactions, peels and interactions by pair of kinds;
#       with two, by the two-stack strategy (kstrat.bend's Two stacks);
#       with ev, evlazy and evtwo, the eager, demand and two-stack
#       strategies running events (knet.bend's Events), counted; with
#       evprofile, the profiling strategy running them, by kind

# the value at the root, interactions, errors, and whether the audits pass:
# the table's live entries match the nodes holding them, the free list the
# free nodes (KN.free_ok), and every live port links a port linking it
# back (KN.wired_ok)
type KRes is Data:
  KRes{v: Maybe<&2, V.Val>, +itrs: U32, +errs: U32, +tab_ok: Bool}

def kres.fl(r: P.H & Bool, +n: U32, +itrs: U32, +errs: U32, +wired: Bool, v: Maybe<&2, V.Val>) -> KRes:
  (h, +free) = r
  KRes{v, itrs, errs, wired && (free && P.h_ok(h, n))}

def kres.wa(r: P.H & Bool, +n: U32, +itrs: U32, +errs: U32, v: Maybe<&2, V.Val>) -> KRes:
  (h, +wired) = r
  kres.fl(KN.free_ok(h), n, itrs, errs, wired, v)

def kres.st(r: P.H & P.HS, +n: U32, v: Maybe<&2, V.Val>) -> KRes:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      kres.wa(KN.wired_ok(h), n, itrs, errs, v)

def kres.au(au: KN.Au, v: Maybe<&2, V.Val>) -> KRes:
  match au:
    case KN.Au{h, +n}:
      kres.st(P.stats(h), n, v)

def kres.h.st(r: P.H & P.HS, v: Maybe<&2, V.Val>) -> KRes:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      kres.au(KN.audit(U32.to_nat((cap - P.first() : U32)), P.first(), KN.Au{h, 0}), v)

def kres.h(h: P.H, v: Maybe<&2, V.Val>) -> KRes:
  kres.h.st(P.stats(h), v)

def kres(r: P.H & Maybe<&2, V.Val>) -> KRes:
  (h, v) = r
  kres.h(h, v)

# reduce t as reduce does, the result as data
def run_t(t: T.Tpl, +fuel: Nat, +fast: Bool) -> KRes:
  kres(KN.result(KS.reduce_h(fuel, fast, KN.load(t))))

# reduce t by the two-stack strategy, the result as data
def run_two(t: T.Tpl, +fuel: Nat, +fast: Bool) -> KRes:
  kres(KN.result(KS.reduce2_h(fuel, fast, KN.load(t))))

# reduce t for at most fuel interactions, by the generated rewrites if
# fast, else by the interpreted table: value and counts
def reduce(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  KN.report(KN.result(KS.reduce_h(fuel, fast, KN.load(t))))

# Erasure modes
# =============
#
# The strategies running events (knet.bend's Events): a result as KRes,
# and the events counted.

type ERes is Data:
  ERes{r: KRes, +evs: U32}

def eres.e(r: P.H & U32, v: Maybe<&2, V.Val>) -> ERes:
  (h, +evs) = r
  ERes{kres.h(h, v), evs}

def eres(r: P.H & Maybe<&2, V.Val>) -> ERes:
  (h, v) = r
  eres.e(P.evs(h), v)

# reduce t as run_t does, running events
def run_ev(t: T.Tpl, +fuel: Nat, +fast: Bool) -> ERes:
  eres(KN.result(KS.reduce_h.v(fuel, fast, KN.load(t))))

# reduce t as run_two does, running events
def run_two_ev(t: T.Tpl, +fuel: Nat, +fast: Bool) -> ERes:
  eres(KN.result(KS.reduce2_h.v(fuel, fast, KN.load(t))))

def ev_str(r: P.H & U32) -> String:
  (h, +evs) = r
  KN.report(KN.result(h)) ++ ", " ++ U32.show(evs) ++ " events"

# reduce t as reduce does, running events, which are counted
def reduce_ev(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  ev_str(P.evs(KS.reduce_h.v(fuel, fast, KN.load(t))))

def prof.k(r: KRes, pf: KS.Pf) -> String:
  match r:
    case KRes{v, +itrs, +errs, +ok}:
      KN.show_val(v) ++ " (" ++ U32.show(itrs) ++ ", " ++ U32.show(errs) ++ "); " ++ KS.pf_str(pf)

def prof(r: P.H & KS.Pf) -> String:
  (h, pf) = r
  prof.k(kres(KN.result(h)), pf)

# reduce t as reduce does, profiled (kstrat.bend's Profiling): value,
# interactions and errors, then the profile
def profile_t(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  prof(KS.reduce_p(fuel, fast, KN.load(t)))

def evk.one(+i: U32, +n: U32) -> String:
  match n:
    case 0:
      ""
    case _:
      " " ++ U32.show(i) ++ ":" ++ U32.show(n)

def evk.r(r: P.H & U32, s: String, +i: U32) -> P.H & String:
  (h, +n) = r
  (h, s ++ evk.one(i, n))

def evk.step(r: P.H & String, +i: U32) -> P.H & String:
  (h, s) = r
  evk.r(P.evk(h, i), s, i)

def evk.go(k: Nat, r: P.H & String, +i: U32) -> P.H & String:
  match k:
    case 0n:
      r
    case 1n+p:
      evk.go(p, evk.step(r, i), (i + 1 : U32))

# the events by the kind code of the node each acted on, ` k:n` for each
# kind with any
def ev_kinds(h: P.H) -> P.H & String:
  evk.go(16n, (h, ""), 0)

def prof_ev.s(r: P.H & String, pf: KS.Pf, +n: U32) -> String:
  (h, s) = r
  prof.k(kres(KN.result(h)), pf) ++ "; events " ++ U32.show(n) ++ " by kind" ++ s

def prof_ev.n(r: P.H & U32, pf: KS.Pf) -> String:
  (h, +n) = r
  prof_ev.s(ev_kinds(h), pf, n)

def prof_ev(r: P.H & KS.Pf) -> String:
  (h, pf) = r
  prof_ev.n(P.evs(h), pf)

# reduce t as profile_t does, running events (KS.reduce_p.v): the profile,
# its logical interactions those of the interactions made, then the
# events, by kind
def profile_ev(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  prof_ev(KS.reduce_p.v(fuel, fast, KN.load(t)))

# Results of demand
# =================

def live.hit(r: P.H & U32, +n: U32) -> KN.Au:
  (h, +hdr) = r
  KN.Au{h, KN.audit.one(U32.is_ne(hdr, 0), n)}

def live(k: Nat, +i: U32, au: KN.Au) -> KN.Au:
  match k:
    case 0n:
      au
    case 1n+p:
      match au:
        case KN.Au{h, +n}:
          live(p, (i + 1 : U32), live.hit(P.rd(h, (i << 2n : U32)), n))

# the nodes still live, the interface's among them
def live_nodes.st(r: P.H & P.HS) -> KN.Au:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      live(U32.to_nat((cap - P.first() : U32)), P.first(), KN.Au{h, 0})

# the value a cell k holds, for a test meeting needs: vals's entry k, a
# unit past its end
def val_at(vs: List<&2, V.Val>, +k: U32) -> V.Val:
  match vs:
    case Nil{}:
      V.VUnit{}
    case Con{v, t}:
      match k:
        case 0:
          v
        case _:
          val_at(t, (k - 1 : U32))

def force.met(r: KS.D & U32, +vals: List<&2, V.Val>) -> KS.D:
  (d, +lz) = r
  KS.resume(d, val_at(vals, lz))

# demand, running events if ev (KS.demand.v)
def demand_ev(+ev: Bool, +fuel: Nat, d: KS.D) -> KS.D:
  match ev:
    case True{}:
      KS.demand.v(fuel, d)
    case False{}:
      KS.demand(fuel, d)

# demand, each need met from vals, at most k times
def force(k: Nat, +fuel: Nat, +ev: Bool, +vals: List<&2, V.Val>, d: KS.D) -> KS.D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case KS.D{h, path, +top, +depth, +n, +st}:
          match st:
            case 2:
              force(p, fuel, ev, vals, demand_ev(ev, fuel, force.met(KS.need(KS.D{h, path, top, depth, n, st}), vals)))
            case _:
              KS.D{h, path, top, depth, n, st}

# a demand's end: the result as reduce_h's, its state, the handle needed,
# the nodes left, how many nodes the net grew to hold, how many of those
# left the interface still reaches (KN.reach)
type DRes is Data:
  DRes{r: KRes, +st: U32, +lz: U32, +live: U32, +cap: U32, +reach: U32}

def dres.cap(r: P.H & P.HS, +st: U32, +lz: U32, +n: U32, +reach: U32) -> DRes:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      DRes{kres(KN.result(h)), st, lz, n, cap, reach}

def dres.r(r: P.H & U32, +st: U32, +lz: U32, +n: U32) -> DRes:
  (h, +reach) = r
  dres.cap(P.stats(h), st, lz, n, reach)

def dres.au(au: KN.Au, +st: U32, +lz: U32) -> DRes:
  match au:
    case KN.Au{h, +n}:
      dres.r(KN.reach(h), st, lz, n)

def dres.h(h: P.H, +st: U32, +lz: U32) -> DRes:
  dres.au(live_nodes.st(P.stats(h)), st, lz)

def dres.l(r: KS.D & U32) -> DRes:
  (d, +lz) = r
  match d:
    case KS.D{h, path, +top, +depth, +n, +st}:
      dres.h(P.count(h, n), st, lz)

def dres(d: KS.D) -> DRes:
  dres.l(KS.need(d))

def dres.sw(r: P.H & U32, +st: U32, +lz: U32) -> DRes:
  (h, +f) = r
  dres.h(h, st, lz)

def dres.sl(r: KS.D & U32) -> DRes:
  (d, +lz) = r
  match d:
    case KS.D{h, path, +top, +depth, +n, +st}:
      dres.sw(KN.sweep(P.count(h, n)), st, lz)

def dres.s(d: KS.D) -> DRes:
  dres.sl(KS.need(d))

# demand, running events if ev, its needs met from vals, at most 64
def demand_m(t: T.Tpl, +fuel: Nat, +ev: Bool, +vals: List<&2, V.Val>) -> KS.D:
  force(64n, fuel, ev, vals, demand_ev(ev, fuel, KS.d.start(KN.load(t))))

# run_d, then every node the interface does not reach freed (KN.sweep)
def run_ds(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> DRes:
  dres.s(demand_m(t, fuel, False{}, vals))

# reduce t toward weak head normal form for at most fuel steps, its needs
# met from vals, at most 64
def run_d(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> DRes:
  dres(demand_m(t, fuel, False{}, vals))

# run_d running events, which are counted
type EDRes is Data:
  EDRes{r: DRes, +evs: U32}

def edres.e(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> EDRes:
  (h, +evs) = r
  EDRes{dres(KS.D{h, path, top, depth, n, st}), evs}

def edres(d: KS.D) -> EDRes:
  match d:
    case KS.D{h, path, +top, +depth, +n, +st}:
      edres.e(P.evs(h), path, top, depth, n, st)

def run_dev(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> EDRes:
  edres(demand_m(t, fuel, True{}, vals))

def st_name(+st: U32) -> String:
  match st:
    case 1:
      "done"
    case 2:
      "needs"
    case 3:
      "stuck"
    case 4:
      "out of fuel"
    case 5:
      "a cycle"
    case _:
      "going"

def kres_str(r: KRes) -> String:
  match r:
    case KRes{v, +itrs, +errs, +ok}:
      KN.show_val(v) ++ ", " ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors" ++ KN.table_str(ok)

def dres_str(r: DRes) -> String:
  match r:
    case DRes{k, +st, +lz, +live, +cap, +reach}:
      st_name(st) ++ KN.need_str(U32.is_eq(st, 2), lz) ++ ": " ++ kres_str(k) ++ ", " ++ U32.show(live) ++ " nodes live of " ++ U32.show(cap) ++
        ", " ++ U32.show(reach) ++ " reached"

# Workloads
# =========

# 0, k 2 succ 0; 1, k 2 (plus 1) 0; 2, k 2 succ 0 with levels; 3,
# k 2 (fma 1 1) 0; 4, K 0 (k 2 succ 0); 5, K 0 applied to the numeral k;
# 6, K 0 applied to a term with no normal form; 7, the numeral k applied
# to succ, a function
def workload(+w: U32, +k: U32) -> T.Tpl:
  match w:
    case 1:
      X.t_pow_plus(k, 2)
    case 2:
      X.t_pow_lvl(k, 2)
    case 3:
      X.t_pow_fma(k, 2)
    case 4:
      X.t_k_pow(k)
    case 5:
      X.t_k_num(k)
    case 6:
      X.t_k_omega()
    case 7:
      X.t_whnf(k)
    case _:
      X.t_pow(k, 2)

# a demand's end as reduce reports a full reduction: its state, the value
# and the counts, without the audits and the walks the tests' results make
def bench_d.l(r: KS.D & U32) -> String:
  (d, +lz) = r
  match d:
    case KS.D{h, path, +top, +depth, +n, +st}:
      st_name(st) ++ KN.need_str(U32.is_eq(st, 2), lz) ++ ": " ++ KN.report(KN.result(P.count(h, n)))

def bench_d(d: KS.D) -> String:
  bench_d.l(KS.need(d))

def bench_dev.e(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> String:
  (h, +evs) = r
  bench_d(KS.D{h, path, top, depth, n, st}) ++ ", " ++ U32.show(evs) ++ " events"

def bench_dev(d: KS.D) -> String:
  match d:
    case KS.D{h, path, +top, +depth, +n, +st}:
      bench_dev.e(P.evs(h), path, top, depth, n, st)

# reduce the workload fully (how 0), on demand (1), profiled (2) or with
# two stacks (4), each measured without the audits; or running events,
# fully (5), on demand (6), with two stacks (7), profiled (8)
def main.run(+how: U32, t: T.Tpl, +fast: Bool) -> String:
  match how:
    case 1:
      bench_d(demand_m(t, 268435456n, False{}, Nil{}))
    case 2:
      profile_t(t, 268435456n, fast)
    case 4:
      KN.report(KN.result(KS.reduce2_h(268435456n, fast, KN.load(t))))
    case 5:
      reduce_ev(t, 268435456n, fast)
    case 6:
      bench_dev(demand_m(t, 268435456n, True{}, Nil{}))
    case 7:
      ev_str(P.evs(KS.reduce2_h.v(268435456n, fast, KN.load(t))))
    case 8:
      profile_ev(t, 268435456n, fast)
    case _:
      reduce(t, 268435456n, fast)

def main.k(+k: U32, +fast: Bool, +w: U32, +how: U32) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = main.run(how, workload(w, k), fast)
    +t1 : Nat <- IO.now()
    IO.print("kernel k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

# a mode: its name, workload, and whether by the generated rewrites
type Md is Data:
  Md{name: String, +w: U32, +fast: Bool}

def modes() -> List<&2, Md>:
  [Md{"succ", 0, True{}}, Md{"ref", 0, False{}}, Md{"plus", 1, True{}}, Md{"plusref", 1, False{}},
   Md{"lvl", 2, True{}}, Md{"lvlref", 2, False{}}, Md{"fma", 3, True{}}, Md{"fmaref", 3, False{}},
   Md{"kpow", 4, True{}}, Md{"knum", 5, True{}}, Md{"komega", 6, True{}}, Md{"whnf", 7, True{}}]

def mode_of.hit(hit: Bool, md: Md, r: Maybe<&2, Md>) -> Maybe<&2, Md>:
  match hit:
    case True{}:
      Some{md}
    case False{}:
      r

def mode_of(ms: List<&2, Md>, +m: String) -> Maybe<&2, Md>:
  match ms:
    case Nil{}:
      None{}
    case Con{Md{+name, +w, +fast}, t}:
      mode_of.hit(String.eq(name, m), Md{name, w, fast}, mode_of(t, m))

def usage() -> String:
  "usage: kernel <k> [succ|ref|plus|plusref|lvl|lvlref|fma|fmaref|kpow|knum|komega|whnf] [lazy|profile|two|ev|evlazy|evtwo|evprofile]"

def main.mode(md: Maybe<&2, Md>, +k: U32, +how: U32) -> IO(Unit):
  match md:
    case Some{Md{name, +w, +fast}}:
      main.k(k, fast, w, how)
    case None{}:
      IO.print(usage())

def how.t(+two: Bool) -> U32:
  match two:
    case True{}:
      4
    case False{}:
      3

def how.p(+profile: Bool, +two: Bool) -> U32:
  match profile:
    case True{}:
      2
    case False{}:
      how.t(two)

# the strategy a third argument names: lazy 1, profile 2, two 4, ev 5,
# evlazy 6, evtwo 7, evprofile 8, else 3 (none)
def how.evp(+evprofile: Bool) -> U32:
  match evprofile:
    case True{}:
      8
    case False{}:
      3

def how.ev(+ev: Bool, +evlazy: Bool, +evtwo: Bool, +evprofile: Bool) -> U32:
  match ev evlazy evtwo:
    case True{} _ _:
      5
    case _ True{} _:
      6
    case _ _ True{}:
      7
    case _ _ _:
      how.evp(evprofile)

def how.e(+how: U32, +l: String) -> U32:
  match how:
    case 3:
      how.ev(String.eq(l, "ev"), String.eq(l, "evlazy"), String.eq(l, "evtwo"), String.eq(l, "evprofile"))
    case _:
      how

def how_of(+lazy: Bool, +profile: Bool, +two: Bool) -> U32:
  match lazy:
    case True{}:
      1
    case False{}:
      how.p(profile, two)

def main.how(md: Maybe<&2, Md>, +k: U32, +how: U32) -> IO(Unit):
  match how:
    case 3:
      IO.print(usage())
    case _:
      main.mode(md, k, how)

def main.rest(+k: U32, xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      main.k(k, True{}, 0, 0)
    case Con{+m, r}:
      match r:
        case Nil{}:
          main.mode(mode_of(modes(), m), k, 0)
        case Con{+l, r2}:
          main.how(mode_of(modes(), m), k, how.e(how_of(String.eq(l, "lazy"), String.eq(l, "profile"), String.eq(l, "two")), l))

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          main.rest(Maybe.default(&2, U32, U32.read(a), 10), r2)
        case Nil{}:
          IO.print(usage())
    case Nil{}:
      IO.print(usage())

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
