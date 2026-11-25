import Base
import ./val.bend as V
import ./tpl.bend as T
import ./kprim.bend as P
import ./knet.bend as KN
import ./kstrat.bend as KS
import ./kdemand.bend as KD
import ./kmem_grow.bend as KM

# The kernel's entry points, which glam and the tests use: a template
# reduced fully by the eager strategy or on demand (kstrat.bend), over the
# net of knet.bend. Its command line, the workloads and their reports, is
# spike/kernel_main.bend, kept apart so that what imports the kernel
# leaves it out (cursor-laws.proofs.imports).

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

def force.met(r: KD.D & U32, +vals: List<&2, V.Val>) -> KD.D:
  (d, +lz) = r
  KS.resume(d, val_at(vals, lz))

# demand by mode: 0 plain (KD.Demand), 1 running events (KD.DemandEv), 2
# collecting where its net would grow (KS.demand.c), 3 collecting as a
# stress test (KS.demand.s)
def demand_ev(+ev: U32, +fuel: Nat, d: KD.D) -> KD.D:
  match ev:
    case 0:
      KD.Demand.demand(fuel, d)
    case 1:
      KD.DemandEv.demand(fuel, d)
    case 2:
      KS.demand.c(fuel, d)
    case _:
      KS.demand.s(fuel, d)

# demand, each need met from vals, at most k times
def force(k: Nat, +fuel: Nat, +ev: U32, +vals: List<&2, V.Val>, d: KD.D) -> KD.D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case KD.D{h, path, +top, +depth, +n, +st}:
          match st:
            case 2:
              force(p, fuel, ev, vals, demand_ev(ev, fuel, force.met(KS.need(KD.D{h, path, top, depth, n, st}), vals)))
            case _:
              KD.D{h, path, top, depth, n, st}

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

def dres.l(r: KD.D & U32) -> DRes:
  (d, +lz) = r
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      dres.h(P.count(h, n), st, lz)

def dres(d: KD.D) -> DRes:
  dres.l(KS.need(d))

def dres.sw(r: P.H & U32, +st: U32, +lz: U32) -> DRes:
  (h, +f) = r
  dres.h(h, st, lz)

def dres.sl(r: KD.D & U32) -> DRes:
  (d, +lz) = r
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      dres.sw(KN.sweep(P.count(h, n)), st, lz)

def dres.s(d: KD.D) -> DRes:
  dres.sl(KS.need(d))

# demand by mode ev, its needs met from vals, at most 64
def demand_m(t: T.Tpl, +fuel: Nat, +ev: U32, +vals: List<&2, V.Val>) -> KD.D:
  force(64n, fuel, ev, vals, demand_ev(ev, fuel, KS.d.start(KN.load(t))))

# run_d, then every node the interface does not reach freed (KN.sweep)
def run_ds(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> DRes:
  dres.s(demand_m(t, fuel, 0, vals))

# reduce t toward weak head normal form for at most fuel steps, its needs
# met from vals, at most 64
def run_d(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> DRes:
  dres(demand_m(t, fuel, 0, vals))

# run_d running events, which are counted
type EDRes is Data:
  EDRes{r: DRes, +evs: U32}

def edres.e(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> EDRes:
  (h, +evs) = r
  EDRes{dres(KD.D{h, path, top, depth, n, st}), evs}

def edres(d: KD.D) -> EDRes:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      edres.e(P.evs(h), path, top, depth, n, st)

def run_dev(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> EDRes:
  edres(demand_m(t, fuel, 1, vals))

# Collecting under demand (heap-strategies.erasure.load.cycle)
# =================
#
# What a collection runs on a net (KS.collect_lean): a walk from the
# interface marking what it reaches and noting the pairs and events
# there, the sweep of what it did not reach, then the noted events and
# collectable pairs. A freshly lowered net has little to give, so
# none is run at load (the maintainer, 2026-11-01); a net under demand has
# its garbage, so demand collects where its net would grow (KS.demand.c).
# Its result is read as demand's, its interactions the total, demand's
# and the collections' (the maintainer: they are part of it), with the
# collections apart: how many ran, their interactions and events, and the
# capacity they scanned, summed.

type CRes is Data:
  CRes{r: DRes, +cyc: U32, +citrs: U32, +cevs: U32, +scan: U32}

def cres.e(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +cyc: U32, +citrs: U32, +scan: U32) -> CRes:
  (h, +cevs) = r
  CRes{dres(KD.D{h, path, top, depth, (n + citrs : U32), st}), cyc, citrs, cevs, scan}

def cres.i(r: P.H & P.HS, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +cyc: U32, +scan: U32) -> CRes:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      cres.e(P.evs(h), path, top, depth, n, st, cyc, itrs, scan)

def cres.s(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +cyc: U32) -> CRes:
  (h, +scan) = r
  cres.i(P.stats(h), path, top, depth, n, st, cyc, scan)

def cres.c(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> CRes:
  (h, +cyc) = r
  cres.s(P.rd(h, P.at_scan()), path, top, depth, n, st, cyc)

def cres(d: KD.D) -> CRes:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      cres.c(P.rd(h, P.at_cyc()), path, top, depth, n, st)

# demand collecting where its net would grow
def run_dc(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> CRes:
  cres(demand_m(t, fuel, 2, vals))

# the same as a stress test, small nets collected far more often
def run_ds.s(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> CRes:
  cres(demand_m(t, fuel, 3, vals))

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
    case 6:
      "out of memory"
    case 7:
      "unscoped"
    case 8:
      "a void"
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
