import Base
import ./val.bend as V
import ./net.bend as N
import ./tpl.bend as T
import ./kernel.bend as K
import ./load.bend as LD

# The kernel's differential test (spike/tools/differential.sh), on terms
# read from a file (heap-strategies.measure.loader): each term through
# the spike, the kernel's interpreted rule table, its generated rewrites
# and on demand, and with events, eager and with two stacks, by both;
# flagging a difference between the table and the rewrites, in value
# with the spike, a table out of step, or demand making more
# interactions than the full reduction. spike/tools/terms.py --kernel
# writes the file (load.bend's format); the program is built once.
#
#   runterms NETS

def show_m(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "fn"
    case None{}:
      "none"

def spike_res(r: N.Q & Maybe<&2, V.Val>) -> K.KRes:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      K.KRes{v, itrs, errs, True{}}

def res_str(r: K.KRes) -> String:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      show_m(v) ++ " (" ++ U32.show(itrs) ++ ", " ++ U32.show(errs) ++ ")"

def res_val(r: K.KRes) -> String:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      show_m(v)

def res_tab(r: K.KRes) -> Bool:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      ok

def verdict(+tab: Bool, +same: Bool, +agree: Bool, +counts: Bool) -> String:
  match tab same agree counts:
    case False{} _ _ _:
      "TABLE MISMATCH"
    case True{} False{} _ _:
      "DIFFER ref/fast"
    case True{} True{} False{} _:
      "DIFFER value"
    case True{} True{} True{} True{}:
      "same, counts equal"
    case True{} True{} True{} False{}:
      "same, counts differ"

def lazy_res(r: K.DRes) -> K.KRes:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      k

# on demand: the state it ended in, the nodes it left
def lazy_st(r: K.DRes) -> String:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      K.st_name(st) ++ ", " ++ U32.show(live) ++ " live"

def lazy_more.s(more: Bool) -> String:
  match more:
    case True{}:
      "  LAZY MORE"
    case False{}:
      ""

def lazy_more(+lz: K.KRes, +fs: K.KRes) -> String:
  match lz fs:
    case K.KRes{v, +i, +e, +ok} K.KRes{v2, +i2, +e2, +ok2}:
      lazy_more.s(U32.is_gt(i, i2))

# with events: the result and the events made
def ev_str(r: K.ERes) -> String:
  match r:
    case K.ERes{r, +evs}:
      res_str(r) ++ " " ++ U32.show(evs)

# with events, eager and with two stacks: the generated rewrites, which
# look at their rules' sites, and the interpreted table, at all four peers
def evs_str(+e: K.ERes, +er: K.ERes, +t: K.ERes, +tr: K.ERes) -> String:
  " | ev " ++ ev_str(e) ++ " / " ++ ev_str(er) ++ " | evtwo " ++ ev_str(t) ++ " / " ++ ev_str(tr)

def cmp.go(+k: U32, +want: U32, name: String, +t: T.Tpl, +sp: K.KRes, +rf: K.KRes, +fs: K.KRes, +lz: K.DRes) -> String:
  "#" ++ U32.show(k) ++ " want " ++ U32.show(want) ++ ": spike " ++ res_str(sp) ++ " | ref " ++ res_str(rf) ++
    " | fast " ++ res_str(fs) ++ " | lazy " ++ res_str(lazy_res(lz)) ++ " " ++ lazy_st(lz) ++
    evs_str(K.run_ev(t, 320000n, True{}), K.run_ev(t, 320000n, False{}),
      K.run_two_ev(t, 320000n, True{}), K.run_two_ev(t, 320000n, False{})) ++ "  " ++
    verdict(res_tab(rf) && res_tab(fs) && res_tab(lazy_res(lz)), String.eq(res_str(rf), res_str(fs)), String.eq(res_val(rf), res_val(sp)), String.eq(res_str(rf), res_str(sp))) ++
    lazy_more(lazy_res(lz), fs) ++ "  " ++ name

# demand's fuel counts the walk's steps too
def cmp_one(+k: U32, r: LD.Row) -> String:
  match r:
    case LD.Row{+t, +want, name}:
      cmp.go(k, want, name, t, spike_res(T.result(T.run(t, 5000n))), K.run_t(t, 320000n, False{}), K.run_t(t, 320000n, True{}),
        K.run_d(t, 1280000n, []))

def cmp_all(rs: List<&2, LD.Row>, +k: U32) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      cmp_one(k, r) ++ "\n" ++ cmp_all(t, (k + 1 : U32))

def main.read(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        IO.print(cmp_all(LD.rows(bs), 0))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("runterms: cannot read the file")

def main.size(fs: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        main.read(fr)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("runterms: cannot size the file")

def main.file(path: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    main.size(fs)

def usage() -> String:
  "usage: runterms NETS"

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{prog, rest}:
      match rest:
        case Con{path, more}:
          main.file(path)
        case Nil{}:
          IO.print(usage())
    case Nil{}:
      IO.print(usage())

# every term through the spike, the kernel's table, its generated rewrites
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
