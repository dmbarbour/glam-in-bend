import Base
import ./parse.bend as G
import ./core.bend as C

# The assembler's shell (pure-core-io-shell), as far as the hello ladder
# has climbed (HelloLadder): one source file read, the core run on its
# bytes slice by slice, `asm.result` written to stdout as bytes, or the
# diagnostics to stderr with exit status 1 (docs/CLI.md: the bootstrap
# compiles only `.g`; any other extension, or none, fails the assembly
# with exit status 1); a command line it cannot read exits 2.
#
#   glam -f FILE.g [--count] [--link] [--refreeze]
#
# With --count, the kernel's interactions over every net reduced, the
# templates spliced, the values forced, the live sources' serves, stops
# and steps walked again, the serves' cursor interactions (a node copied
# each) and the nodes the splices made are reported on stderr, for the
# store (HelloLadder's ladder-measure). With --link, every definition is
# linked statically, top-level functions too, as before templates, for a
# differential run (glam/core.bend). With --refreeze, every template is
# loaded and frozen back before the run, a check of freezing.

def usage() -> String:
  "usage: glam -f FILE.g [--count] [--link] [--refreeze]"

def diag_str.k(+no_line: Bool, +line: U32, msg: String) -> String:
  match no_line:
    case True{}:
      "error: " ++ msg
    case False{}:
      "error at line " ++ U32.show(line) ++ ": " ++ msg

def diag_str(d: G.Diag) -> String:
  match d:
    case G.Diag{+line, msg}:
      diag_str.k(U32.is_eq(line, 0), line, msg)

def report(ds: List<&2, G.Diag>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.exit(1)
    case Con{d, rest}:
      do IO<Unit>:
        IO.print_err(diag_str(d))
        report(rest)

def wrote(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  match res:
    case Done{u}:
      File.close(f)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print_err("glam: cannot write to stdout")
        IO.exit(1)

# the bytes to stdout, binary-safe through a File on /dev/stdout
# (IO.write encodes a String as UTF-8), opened to append: opened to write,
# a stdout that is a file would be truncated (docs/BendIssues.md, Binary
# output to standard output)
def emit(bs: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdout", "a"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, bs)
    wrote(r)

def counted(+count: Bool, +itrs: U32, +sp: U32, +fo: U32, +sv: U32, +st: U32, +rw: U32, +cp: U32, +sn: U32, bs: List<&2, U32>) -> IO(Unit):
  match count:
    case True{}:
      do IO<Unit>:
        IO.print_err(U32.show(itrs) ++ " interactions, " ++ U32.show(sp) ++ " splices, " ++ U32.show(fo) ++ " values forced, " ++ U32.show(sv) ++ " serves, " ++ U32.show(st) ++ " source stops, " ++ U32.show(rw) ++ " steps walked again, " ++ U32.show(cp) ++ " cursor interactions, " ++ U32.show(sn) ++ " nodes spliced")
        emit(bs)
    case False{}:
      emit(bs)

def finish(o: C.Out, +count: Bool) -> IO(Unit):
  match o:
    case C.OBytes{bs, +itrs, +sp, +fo, +sv, +st, +rw, +cp, +sn}:
      counted(count, itrs, sp, fo, sv, st, rw, cp, sn, bs)
    case C.OErrs{ds}:
      report(ds)

# 2^47 slices: Bend requires every loop to end, IO's too (an IO loop
# with no shrinking argument is refused, and @unsafe would take the shell
# out of the proofs), so the shell counts this down; at a million steps
# a slice, no assembly reaches it. A Nat packs below 2^48, a literal
# below 2^32.
def budget() -> Nat:
  Nat.mul(65536n, Nat.mul(65536n, 32768n))

# the assembly stepped slice by slice until done
def slices(left: Nat, r: C.Run, +count: Bool) -> IO(Unit):
  match left:
    case 0n:
      do IO<Unit>:
        IO.print_err("glam: the assembly ran past its budget of slices")
        IO.exit(1)
    case 1n+more:
      match r:
        case C.RDone{o}:
          finish(o, count)
        case C.RMore{t, s, b, c, ss}:
          slices(more, C.step(t, s, b, c, ss), count)

def read(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, +count: Bool, +lk: Bool, +rf: Bool) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        slices(budget(), C.refrozen(rf, C.start(bs, lk)), count)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print_err("glam: cannot read the file")
        IO.exit(1)

def sized(fs: File & Result<&1, &1, U32 & String, U32>, +count: Bool, +lk: Bool, +rf: Bool) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        read(fr, count, lk, rf)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print_err("glam: cannot size the file")
        IO.exit(1)

def opened(r: Result<&1, &1, U32 & String, File>, +count: Bool, +lk: Bool, +rf: Bool) -> IO(Unit):
  match r:
    case Done{f}:
      do IO<Unit>:
        fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        sized(fs, count, lk, rf)
    case Fail{e}:
      do IO<Unit>:
        IO.print_err("glam: cannot open the file")
        IO.exit(1)

def source(+is_g: Bool, path: String, +count: Bool, +lk: Bool, +rf: Bool) -> IO(Unit):
  match is_g:
    case True{}:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        opened(r, count, lk, rf)
    case False{}:
      do IO<Unit>:
        IO.print_err("glam: the bootstrap compiles only .g files: " ++ path)
        IO.exit(1)

# the arguments read: the path after `-f`, and whether `--count`,
# `--link` and `--refreeze` were given
type Args is Type:
  Args{file: Maybe<&1, String>, +count: Bool, +lk: Bool, +rf: Bool}

def file_arg(+want: Bool, a: String) -> Maybe<&1, String>:
  match want:
    case True{}:
      Some{a}
    case False{}:
      None{}

# the arguments walked once (an affine list), with whether the last was
# `-f` and what was found so far
def args.go(xs: List<String>, +want: Bool, found: Maybe<&1, String>, +count: Bool, +lk: Bool, +rf: Bool) -> Args:
  match xs:
    case Nil{}:
      Args{found, count, lk, rf}
    case Con{+a, rest}:
      match found:
        case Some{p}:
          args.go(rest, False{}, Some{p}, count || String.eq(a, "--count"), lk || String.eq(a, "--link"), rf || String.eq(a, "--refreeze"))
        case None{}:
          args.go(rest, String.eq(a, "-f"), file_arg(want, a), count || String.eq(a, "--count"), lk || String.eq(a, "--link"), rf || String.eq(a, "--refreeze"))

def run(m: Maybe<&1, String>, +count: Bool, +lk: Bool, +rf: Bool) -> IO(Unit):
  match m:
    case Some{+path}:
      source(String.ends_with(path, ".g"), path, count, lk, rf)
    case None{}:
      do IO<Unit>:
        IO.print_err(usage())
        IO.exit(2)

def run.args(r: Args) -> IO(Unit):
  match r:
    case Args{file, +count, +lk, +rf}:
      run(file, count, lk, rf)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    run.args(args.go(xs, False{}, None{}, False{}, False{}, False{}))
