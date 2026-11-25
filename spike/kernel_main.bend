# The kernel's command line: `bend spike/kernel_main.bend -o kernel`, its
# workloads at k, reduced fully, on demand, profiled or with events
# (`usage`). Kept apart from spike/kernel.bend, the kernel the rest of
# glam imports, so that a proof importing the kernel leaves this out: it
# was more than half of what a verdict translated for it
# (cursor-laws.proofs.imports, 2026-11-25).
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

import Base
import ./tpl.bend as T
import ./nets.bend as X
import ./kprim.bend as P
import ./knet.bend as KN
import ./kstrat.bend as KS
import ./kdemand.bend as KD
import ./kmem_grow.bend as KM
import ./kernel.bend as K

def ev_str(r: P.H & U32) -> String:
  (h, +evs) = r
  KN.report(KN.result(h)) ++ ", " ++ U32.show(evs) ++ " events"

# reduce t as reduce does, running events, which are counted
def reduce_ev(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  ev_str(P.evs(KS.reduce_h.v(fuel, fast, KN.load(t))))

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
def bench_d.l(r: KD.D & U32) -> String:
  (d, +lz) = r
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      K.st_name(st) ++ KN.need_str(U32.is_eq(st, 2), lz) ++ ": " ++ KN.report(KN.result(P.count(h, n)))

def bench_d(d: KD.D) -> String:
  bench_d.l(KS.need(d))

def bench_dev.e(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> String:
  (h, +evs) = r
  bench_d(KD.D{h, path, top, depth, n, st}) ++ ", " ++ U32.show(evs) ++ " events"

def bench_dev(d: KD.D) -> String:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      bench_dev.e(P.evs(h), path, top, depth, n, st)

def bench_dc.s(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +citrs: U32, +cyc: U32) -> String:
  (h, +scan) = r
  bench_dev(KD.D{h, path, top, depth, (n + citrs : U32), st}) ++ ", " ++ U32.show(cyc) ++ " collections, " ++
    U32.show(citrs) ++ " interactions collecting, " ++ U32.show(scan) ++ " nodes scanned"

def bench_dc.c(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +citrs: U32) -> String:
  (h, +cyc) = r
  bench_dc.s(P.rd(h, P.at_scan()), path, top, depth, n, st, citrs, cyc)

def bench_dc.i(r: P.H & P.HS, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> String:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      bench_dc.c(P.rd(h, P.at_cyc()), path, top, depth, n, st, itrs)

# demand collecting where its net would grow, its interactions the total,
# its collections counted
def bench_dc(d: KD.D) -> String:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      bench_dc.i(P.stats(h), path, top, depth, n, st)

# reduce the workload fully (how 0), on demand (1), profiled (2) or with
# two stacks (4), each measured without the audits; or running events,
# fully (5), on demand (6), with two stacks (7), profiled (8); or on demand
# collecting where the net would grow (9)
def main.run(+how: U32, t: T.Tpl, +fast: Bool) -> String:
  match how:
    case 1:
      bench_d(K.demand_m(t, 268435456n, 0, Nil{}))
    case 2:
      K.profile_t(t, 268435456n, fast)
    case 4:
      KN.report(KN.result(KS.reduce2_h(268435456n, fast, KN.load(t))))
    case 5:
      reduce_ev(t, 268435456n, fast)
    case 6:
      bench_dev(K.demand_m(t, 268435456n, 1, Nil{}))
    case 7:
      ev_str(P.evs(KS.reduce2_h.v(268435456n, fast, KN.load(t))))
    case 8:
      K.profile_ev(t, 268435456n, fast)
    case 9:
      bench_dc(K.demand_m(t, 268435456n, 2, Nil{}))
    case _:
      K.reduce(t, 268435456n, fast)

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
  "usage: kernel <k> [succ|ref|plus|plusref|lvl|lvlref|fma|fmaref|kpow|knum|komega|whnf] [lazy|profile|two|ev|evlazy|evtwo|evprofile|dclazy]"

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
# evlazy 6, evtwo 7, evprofile 8, dclazy 9, else 3 (none)
def how.evp(+evprofile: Bool, +dclazy: Bool) -> U32:
  match evprofile dclazy:
    case True{} _:
      8
    case _ True{}:
      9
    case _ _:
      3

def how.ev(+ev: Bool, +evlazy: Bool, +evtwo: Bool, +evprofile: Bool, +dclazy: Bool) -> U32:
  match ev evlazy evtwo:
    case True{} _ _:
      5
    case _ True{} _:
      6
    case _ _ True{}:
      7
    case _ _ _:
      how.evp(evprofile, dclazy)

def how.e(+how: U32, +l: String) -> U32:
  match how:
    case 3:
      how.ev(String.eq(l, "ev"), String.eq(l, "evlazy"), String.eq(l, "evtwo"), String.eq(l, "evprofile"), String.eq(l, "dclazy"))
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
