import Base
import ./tpl.bend as T
import ./kernel.bend as K
import ./load.bend as LD

# Demand in one mode on terms read from a file (load.bend's format), for
# counting a mode's instructions on workloads that drop what they make
# (heap-strategies.erasure.load.cycle): the library's entries, written by
# spike/tools/library_nets.py, or random terms (terms.py --kernel gen).
# Plain demand (lazy), demand collecting where its net would grow
# (dclazy), or its stress test, collecting a net of 1024 nodes or fewer
# every 16 steps (dcs, heap-strategies.erasure.load.cycle.stress); each
# term's state, value, interactions and capacity, and the collections'
# count, interactions and nodes scanned.
#
#   runmode NETS lazy|dclazy|dcs

def one.d(r: K.DRes) -> String:
  K.dres_str(r)

def one.c(r: K.CRes) -> String:
  match r:
    case K.CRes{k, +cyc, +citrs, +cevs, +scan}:
      K.dres_str(k) ++ "; " ++ U32.show(cyc) ++ " collections, " ++ U32.show(citrs) ++ " interactions, " ++
        U32.show(scan) ++ " nodes scanned"

# by mode: 0 plain, 1 collecting, 2 its stress test
def one.r(+m: U32, t: T.Tpl) -> String:
  match m:
    case 0:
      one.d(K.run_d(t, 2560000n, []))
    case 1:
      one.c(K.run_dc(t, 2560000n, []))
    case _:
      one.c(K.run_ds.s(t, 2560000n, []))

def one(+m: U32, r: LD.Row) -> String:
  match r:
    case LD.Row{t, +want, name}:
      name ++ ": " ++ one.r(m, t)

def all(+m: U32, rs: List<&2, LD.Row>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      one(m, r) ++ "\n" ++ all(m, t)

def main.read(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, +dc: U32) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        IO.print(all(dc, LD.rows(bs)))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("runmode: cannot read the file")

def main.size(fs: File & Result<&1, &1, U32 & String, U32>, +dc: U32) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        main.read(fr, dc)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("runmode: cannot size the file")

def main.file(path: String, +dc: U32) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    main.size(fs, dc)

def usage() -> String:
  "usage: runmode NETS lazy|dclazy|dcs"

def main.mode(path: String, +lazy: Bool, +dc: Bool, +dcs: Bool) -> IO(Unit):
  match lazy dc dcs:
    case True{} _ _:
      main.file(path, 0)
    case _ True{} _:
      main.file(path, 1)
    case _ _ True{}:
      main.file(path, 2)
    case _ _ _:
      IO.print(usage())

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{prog, rest}:
      match rest:
        case Con{path, more}:
          match more:
            case Con{+m, r}:
              main.mode(path, String.eq(m, "lazy"), String.eq(m, "dclazy"), String.eq(m, "dcs"))
            case Nil{}:
              IO.print(usage())
        case Nil{}:
          IO.print(usage())
    case Nil{}:
      IO.print(usage())

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
