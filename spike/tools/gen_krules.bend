import Base
import ../rules.bend as R
import ../net.bend as N

# Writes spike/krules.bend: the kernel's rewrites, generated from the rule
# table (R.rule), so the rules that run are the rules the laws are proved
# over (spike-node-layout in docs/plans/EvalSpike_2026-10-26.md; the
# workaround for compile-time specialization in docs/BendIssues.md).
# scripts/check.sh regenerates the file and fails on any difference.
#
#   bend spike/tools/gen_krules.bend > spike/krules.bend
#
# A rule becomes a chain of functions: the first frees the redex and makes
# the first new node; step j takes node j - 1 and makes node j; the last
# step links, in the table's order. The chain is written last step first,
# a callee preceding its caller. The code assumes no external peer is a
# port of the redex itself; the kernel sends such redexes through its
# interpreter of the table instead.

def kinds() -> List<&2, R.NodeKind>:
  [R.KFree{}, R.KFn{}, R.KAp{}, R.KCopy{}, R.KMerge{}, R.KData{}, R.KEraN{}, R.KEraP{}, R.KRoot{}, R.KCall{}, R.KLift{}, R.KLiftC{}]

def kname(k: R.NodeKind) -> String:
  match k:
    case R.KFree{}:
      "Free"
    case R.KFn{}:
      "Fn"
    case R.KAp{}:
      "Ap"
    case R.KCopy{}:
      "Copy"
    case R.KMerge{}:
      "Merge"
    case R.KData{}:
      "Data"
    case R.KEraN{}:
      "EraN"
    case R.KEraP{}:
      "EraP"
    case R.KRoot{}:
      "Root"
    case R.KCall{}:
      "Call"
    case R.KLift{}:
      "Lift"
    case R.KLiftC{}:
      "LiftC"

def code(+k: R.NodeKind) -> String:
  U32.show(N.kcode(k))

def is_data(k: R.NodeKind) -> Bool:
  match k:
    case R.KData{}:
      True{}
    case R.KCall{}:
      True{}
    case _:
      False{}

# a new node's header and payload word, by source; a payload carries its
# value form with it (SApply's value is made by a step of its own)
def hdr(+k: R.NodeKind, s: R.Src) -> String:
  match s:
    case R.SPayA{}:
      "P.hd2(" ++ code(k) ++ ", P.form(ha), P.fld(ha))"
    case R.SPayB{}:
      "P.hd2(" ++ code(k) ++ ", P.form(hb), P.fld(hb))"
    case R.SFanA{}:
      "P.hd(" ++ code(k) ++ ", P.fld(ha))"
    case R.SFanB{}:
      "P.hd(" ++ code(k) ++ ", P.fld(hb))"
    case R.SLiftA{}:
      "P.hd(" ++ code(k) ++ ", P.lift(P.fld(hb), pb, P.fld(ha)))"
    case R.SLiftB{}:
      "P.hd(" ++ code(k) ++ ", P.lift(P.fld(ha), pa, P.fld(hb)))"
    case _:
      "P.hd(" ++ code(k) ++ ", 0)"

def pword(s: R.Src) -> String:
  match s:
    case R.SPayA{}:
      "pa"
    case R.SPayB{}:
      "pb"
    case R.SLiftA{}:
      "pa"
    case R.SLiftB{}:
      "pb"
    case _:
      "0"

def is_apply(s: R.Src) -> Bool:
  match s:
    case R.SApply{}:
      True{}
    case _:
      False{}

def spec_kind(sp: R.Spec) -> R.NodeKind:
  match sp:
    case R.Spec{+k, s}:
      k

def spec_at(xs: List<&2, R.Spec>, j: Nat) -> R.Spec:
  match xs j:
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+i:
      spec_at(t, i)
    case Nil{} _:
      R.Spec{R.KFree{}, R.SNone{}}

# a reference to port p of new node j
def new_end(+j: Nat, +p: Nat) -> String:
  match p:
    case 0n:
      "n" ++ Nat.show(j)
    case _:
      "(n" ++ Nat.show(j) ++ " + " ++ Nat.show(p) ++ " : U32)"

def end(+xs: List<&2, R.Spec>, e: R.End) -> String:
  match e:
    case R.Ext{i}:
      "e" ++ Nat.show(i)
    case R.New{+j, +p}:
      new_end(j, p)

def links(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{R.Link{u, v}, t}:
      links(xs, t, "P.link(" ++ acc ++ ", " ++ end(xs, u) ++ ", " ++ end(xs, v) ++ ")")

def common() -> String:
  "+a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32"

def common_args() -> String:
  "a, b, ha, hb, pa, pb, e0, e1, e2, e3"

# parameters, and arguments, n0 .. n(j - 1)
def made_params(j: Nat, +i: Nat) -> String:
  match j:
    case 0n:
      ""
    case 1n+p:
      ", +n" ++ Nat.show(i) ++ ": U32" ++ made_params(p, 1n+i)

def made_args(j: Nat, +i: Nat) -> String:
  match j:
    case 0n:
      ""
    case 1n+p:
      ", n" ++ Nat.show(i) ++ made_args(p, 1n+i)

def stepname(+name: String, +j: Nat) -> String:
  name ++ ".k" ++ Nat.show(j)

# Linear payloads
# ---------------
#
# A data node's or a call's payload may be a table entry with one owner:
# the first new node using it takes it over, each later one gets a
# duplicate, and a rule using it nowhere drops it. SApply takes both.

def uses_a(s: R.Src) -> Nat:
  match s:
    case R.SPayA{}:
      1n
    case _:
      0n

def uses_b(s: R.Src) -> Nat:
  match s:
    case R.SPayB{}:
      1n
    case _:
      0n

def uses_x(+isa: Bool, s: R.Src) -> Nat:
  match isa:
    case True{}:
      uses_a(s)
    case False{}:
      uses_b(s)

# uses of A's (isa) or B's payload among the first j specs
def uses(xs: List<&2, R.Spec>, +isa: Bool, j: Nat) -> Nat:
  match xs j:
    case Con{R.Spec{k, s}, t} 1n+i:
      Nat.add(uses_x(isa, s), uses(t, isa, i))
    case _ _:
      0n

def has_apply(xs: List<&2, R.Spec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{R.Spec{k, s}, t}:
      is_apply(s) || has_apply(t)

# kinds of step before making a node: none, computing, duplicating
type Pre is Data:
  PNo{}
  PAp{}
  PDup{+isa: Bool}

def pre_x(+dup: Bool, +isa: Bool) -> Pre:
  match dup:
    case True{}:
      PDup{isa}
    case False{}:
      PNo{}

def pre_of(sp: R.Spec, +xs: List<&2, R.Spec>, +j: Nat, +a: R.NodeKind, +b: R.NodeKind) -> Pre:
  match sp:
    case R.Spec{k, s}:
      match s:
        case R.SApply{}:
          PAp{}
        case R.SPayA{}:
          pre_x(is_data(a) && Nat.is_gt(uses(xs, True{}, j), 0n), True{})
        case R.SPayB{}:
          pre_x(is_data(b) && Nat.is_gt(uses(xs, False{}, j), 0n), False{})
        case _:
          PNo{}

def side(+isa: Bool) -> String:
  match isa:
    case True{}:
      "a"
    case False{}:
      "b"

# making node j (spec sp, step kind pre) on state `st`, then step j + 1
def make_call(+name: String, +st: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          stepname(name, 1n+j) ++ "(P.node(" ++ st ++ ", " ++ hdr(k, s) ++ ", " ++ pword(s) ++ "), " ++ common_args() ++ made_args(j, 0n) ++ ")"
        case PAp{}:
          stepname(name, 1n+j) ++ ".pre(P.apply(" ++ st ++ ", ha, pa, hb, pb), " ++ common_args() ++ made_args(j, 0n) ++ ")"
        case PDup{+isa}:
          stepname(name, 1n+j) ++ ".pre(P.dup(" ++ st ++ ", P.form(h" ++ side(isa) ++ "), p" ++ side(isa) ++ "), " ++ common_args() ++ made_args(j, 0n) ++ ")"

# the step taking a computed value or a duplicate, making node j
def pre_fn(+name: String, +j: Nat, sp: R.Spec, pre: Pre) -> String:
  match sp:
    case R.Spec{+k, +s}:
      match pre:
        case PNo{}:
          ""
        case PAp{}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(r: P.H & P.PW, " ++ common() ++ made_params(j, 0n) ++ ") -> P.H:\n" ++
            "  (h, pw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(P.node_pw(h, " ++ code(k) ++ ", pw), " ++ common_args() ++ made_args(j, 0n) ++ ")\n\n"
        case PDup{+isa}:
          "def " ++ stepname(name, 1n+j) ++ ".pre(r: P.H & U32, " ++ common() ++ made_params(j, 0n) ++ ") -> P.H:\n" ++
            "  (h, +dw) = r\n" ++
            "  " ++ stepname(name, 1n+j) ++ "(P.node(h, " ++ hdr(k, s) ++ ", dw), " ++ common_args() ++ made_args(j, 0n) ++ ")\n\n"

def step_body(last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      links(xs, ls, "h")
    case False{}:
      make_call(name, "h", j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

def step_pre(last: Bool, +name: String, +j: Nat, +xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match last:
    case True{}:
      ""
    case False{}:
      pre_fn(name, j, spec_at(xs, j), pre_of(spec_at(xs, j), xs, j, a, b))

# step j (1 .. n), taking node j - 1
def step_fn(+name: String, +j: Nat, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  step_pre(Nat.is_ge(j, n), name, j, xs, a, b) ++
  "def " ++ stepname(name, j) ++ "(r: P.H & U32, " ++ common() ++ made_params(Nat.sub(j, 1n), 0n) ++ ") -> P.H:\n" ++
    "  (h, +n" ++ Nat.show(Nat.sub(j, 1n)) ++ ") = r\n" ++
    "  " ++ step_body(Nat.is_ge(j, n), name, j, xs, ls, a, b) ++ "\n\n"

# steps m down to 1
def steps(+m: Nat, +name: String, +n: Nat, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match m:
    case 0n:
      ""
    case 1n+p:
      step_fn(name, m, n, xs, ls, a, b) ++ steps(p, name, n, xs, ls, a, b)

def drop_if(d: Bool, +st: String, +isa: Bool) -> String:
  match d:
    case True{}:
      "P.drop(" ++ st ++ ", P.form(h" ++ side(isa) ++ "), p" ++ side(isa) ++ ")"
    case False{}:
      st

# the state after freeing the redex: a data payload no new node uses,
# dropped
def start(+xs: List<&2, R.Spec>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  drop_if(is_data(b) && Nat.is_eq(uses(xs, False{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
    drop_if(is_data(a) && Nat.is_eq(uses(xs, True{}, List.length(&2, R.Spec, xs)), 0n) && Bool.not(has_apply(xs)),
      "P.fresh2(h, a, b)", True{}), False{})

def entry(+name: String, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match xs:
    case Nil{}:
      "def " ++ name ++ "(h: P.H, " ++ common() ++ ") -> P.H:\n" ++
        "  " ++ links(xs, ls, start(xs, a, b)) ++ "\n\n"
    case Con{sp, t}:
      steps(List.length(&2, R.Spec, xs), name, List.length(&2, R.Spec, xs), xs, ls, a, b) ++
        pre_fn(name, 0n, sp, pre_of(sp, xs, 0n, a, b)) ++
        "def " ++ name ++ "(h: P.H, " ++ common() ++ ") -> P.H:\n" ++
        "  " ++ make_call(name, start(xs, a, b), 0n, sp, pre_of(sp, xs, 0n, a, b)) ++ "\n\n"

# a rule's functions, the first named `name`
def rule_fns(r: R.Rule, +name: String, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match r:
    case R.RStuck{}:
      ""
    case R.RWire{+xs, +ls}:
      entry(name, xs, ls, a, b)

def is_stuck(r: R.Rule) -> Bool:
  match r:
    case R.RStuck{}:
      True{}
    case _:
      False{}

def call.s(st: Bool, +name: String) -> String:
  match st:
    case True{}:
      "P.err_if(U32.is_ne(ka, 8), h)"
    case False{}:
      name ++ "(h, " ++ common_args() ++ ")"

def call(r: R.Rule, +name: String) -> String:
  call.s(is_stuck(r), name)

# Pairs
# =====

def pname(+a: R.NodeKind, +b: R.NodeKind) -> String:
  "rw." ++ kname(a) ++ "." ++ kname(b)

# do the rule's two variants, for t true and false, differ?
def differs(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  Bool.not(String.eq(rule_fns(R.rule(a, b, True{}), "x", a, b), rule_fns(R.rule(a, b, False{}), "x", a, b)))

def both_stuck(+a: R.NodeKind, +b: R.NodeKind) -> Bool:
  is_stuck(R.rule(a, b, True{})) && is_stuck(R.rule(a, b, False{}))

def pair_fns.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      rule_fns(R.rule(a, b, True{}), pname(a, b) ++ ".yes", a, b) ++ rule_fns(R.rule(a, b, False{}), pname(a, b) ++ ".no", a, b)
    case False{}:
      rule_fns(R.rule(a, b, False{}), pname(a, b), a, b)

def pair_fns(+a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_fns.d(differs(a, b), a, b)

def pair_case.d(d: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match d:
    case True{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      match t:\n" ++
      "        case True{}:\n" ++
      "          " ++ call(R.rule(a, b, True{}), pname(a, b) ++ ".yes") ++ "\n" ++
      "        case False{}:\n" ++
      "          " ++ call(R.rule(a, b, False{}), pname(a, b) ++ ".no") ++ "\n"
    case False{}:
      "    case " ++ code(a) ++ " " ++ code(b) ++ ":\n" ++
      "      " ++ call(R.rule(a, b, False{}), pname(a, b)) ++ "\n"

def pair_case.s(s: Bool, +a: R.NodeKind, +b: R.NodeKind) -> String:
  match s:
    case True{}:
      ""
    case False{}:
      pair_case.d(differs(a, b), a, b)

def pair_case(+a: R.NodeKind, +b: R.NodeKind) -> String:
  pair_case.s(both_stuck(a, b), a, b)

def pick(b: Bool, +x: String, +y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def over_b(bs: List<&2, R.NodeKind>, +a: R.NodeKind, +fns: Bool) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      pick(fns, pair_fns(a, b), pair_case(a, b)) ++ over_b(t, a, fns)

def over_a(as: List<&2, R.NodeKind>, +fns: Bool) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      over_b(kinds(), a, fns) ++ over_a(t, fns)

def neg_str.b(b: Bool) -> String:
  match b:
    case True{}:
      "True{}"
    case False{}:
      "False{}"

def neg_str(+k: R.NodeKind) -> String:
  neg_str.b(R.pol_eq(R.port_pol(k, 0n), R.Neg{}))

def tables.k(ks: List<&2, R.NodeKind>, +neg: Bool) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{+k, t}:
      "    case " ++ code(k) ++ ":\n      " ++ pick(neg, neg_str(k), U32.show(U32.from_nat(R.arity(k)))) ++ "\n" ++ tables.k(t, neg)

# ports and principal polarity by kind code (R.arity, R.port_pol)
def tables() -> String:
  "# ports by kind code (R.arity)\n" ++
  "def kind_arity(+k: U32) -> U32:\n  match k:\n" ++ tables.k(kinds(), False{}) ++ "    case _:\n      0\n\n" ++
  "# is the principal port negative? (R.port_pol)\n" ++
  "def kind_neg(+k: U32) -> Bool:\n  match k:\n" ++ tables.k(kinds(), True{}) ++ "    case _:\n      False{}\n\n"

def file() -> String:
  "import Base\n" ++
  "import ./kprim.bend as P\n\n" ++
  "# The kernel's rewrites, generated from the rule table (spike/rules.bend)\n" ++
  "# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if\n" ++
  "# this file differs from what the generator writes.\n\n" ++
  tables() ++
  over_a(kinds(), True{}) ++
  "# the rewrite for A, negative principal, meeting B; t is the payload test\n" ++
  "def rewrite(+ka: U32, +kb: U32, +t: Bool, h: P.H, " ++ common() ++ ") -> P.H:\n" ++
  "  match ka kb:\n" ++
  over_a(kinds(), False{}) ++
  "    case _ _:\n" ++
  "      P.err_if(U32.is_ne(ka, 8), h)\n"

def main() -> IO(Unit):
  IO.print(file())
