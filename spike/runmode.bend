import Base
import ./tpl.bend as T
import ./kernel.bend as K
import ./load.bend as LD

# Demand in one mode on terms read from a file (load.bend's format), for
# counting a mode's instructions on workloads that drop what they make
# (heap-strategies.erasure.load.cycle): the library's entries, written by
# spike/tools/library_nets.py. Plain demand (lazy) or demand collecting
# where its net would grow (dclazy); each term's state, value,
# interactions and capacity, and the collections' count, interactions and
# nodes scanned.
#
#   runmode NETS lazy|dclazy

def one.d(r: K.DRes) -> String:
  K.dres_str(r)

def one.c(r: K.CRes) -> String:
  match r:
    case K.CRes{k, +cyc, +citrs, +cevs, +scan}:
      K.dres_str(k) ++ "; " ++ U32.show(cyc) ++ " collections, " ++ U32.show(citrs) ++ " interactions, " ++
        U32.show(scan) ++ " nodes scanned"

def one.r(+dc: Bool, t: T.Tpl) -> String:
  match dc:
    case True{}:
      one.c(K.run_dc(t, 2560000n, []))
    case False{}:
      one.d(K.run_d(t, 2560000n, []))

def one(+dc: Bool, r: LD.Row) -> String:
  match r:
    case LD.Row{t, +want, name}:
      name ++ ": " ++ one.r(dc, t)

def all(+dc: Bool, rs: List<&2, LD.Row>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      one(dc, r) ++ "\n" ++ all(dc, t)

def main.read(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, +dc: Bool) -> IO(Unit):
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

def main.size(fs: File & Result<&1, &1, U32 & String, U32>, +dc: Bool) -> IO(Unit):
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

def main.file(path: String, +dc: Bool) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    main.size(fs, dc)

def usage() -> String:
  "usage: runmode NETS lazy|dclazy"

def main.mode(path: String, +lazy: Bool, +dc: Bool) -> IO(Unit):
  match lazy dc:
    case True{} _:
      main.file(path, False{})
    case _ True{}:
      main.file(path, True{})
    case _ _:
      IO.print(usage())

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{prog, rest}:
      match rest:
        case Con{path, more}:
          match more:
            case Con{+m, r}:
              main.mode(path, String.eq(m, "lazy"), String.eq(m, "dclazy"))
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
