import Base
import ./lex.bend as L
import ./layout.bend as Y

# The ".g" parser, as far as the hello ladder has climbed (HelloLadder,
# ladder-text): the language declaration first (docs/Syntax.md, Language
# Version Declaration), then definitions `path = Expr`, each declaration
# beginning at column 0 and continuing on indented lines (Toplevel
# Structure). Expressions, as far as the ladder reaches: texts, decimal
# numbers, names and dotted paths, list literals, parentheses, and the
# infix `++` (ladder-lists), `let` and `where` binding groups
# (ladder-locals), their layout made explicit by glam/layout.bend, and
# lambdas, application and parameters on definitions
# (ladder-lambda.functions).
# Diagnostics carry the line of the token at
# fault, as samples/invalid's .expect files name them; every declaration
# is read, so that one file reports all its errors.
#
# Bend admits no mutual recursion and no match on a computed value, so
# each loop here is one function recurring on its list, the step it takes
# computed by a helper into a value the next call matches as a parameter.

type Expr is Data:
  EText{s: List<&2, U32>}
  ENum{+n: U32}
  EList{xs: List<&2, Expr>}
  # a name, or a dotted path of names
  EName{+line: U32, path: List<&2, List<&2, U32>>}
  # an infix operator applied, at the operator's line
  EOp2{+line: U32, op: List<&2, U32>, a: Expr, b: Expr}
  # a binding group, `let`'s or `where`'s, at its keyword's line: its
  # bindings as a chain of EBind ending in EIn, the body they scope, so
  # that one recursion walks the group
  ELet{+line: U32, group: Expr}
  EBind{+line: U32, name: List<&2, U32>, value: Expr, rest: Expr}
  EIn{body: Expr}
  # a lambda of one parameter, and an application: what a binding group
  # becomes (glam/desugar.bend), and soon what `\x -> e` and `f x` parse to
  ELam{+line: U32, name: List<&2, U32>, body: Expr}
  EApp{+line: U32, f: Expr, x: Expr}
  # a builtin by its op and the arguments it needs: what `++` becomes
  EBuiltin{+op: U32, +need: U32}

# a definition: its line, its path (`asm.result` is [asm, result]), its
# body
type Def is Data:
  Def{+line: U32, path: List<&2, List<&2, U32>>, body: Expr}

type Diag is Data:
  Diag{+line: U32, msg: String}

type Mod is Data:
  Mod{+utf8: Bool, defs: List<&2, Def>}

type Parsed is Data:
  POk{m: Mod}
  PErr{ds: List<&2, Diag>}

# Text
# ====

def str(bs: List<&2, U32>) -> String:
  match bs:
    case Con{+b, rest}:
      SCon{Char.from_u32(b), str(rest)}
    case Nil{}:
      SNil{}

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Con{+x, xs} Con{+y, ys}:
      U32.is_eq(x, y) && bytes_eq(xs, ys)
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def path_eq(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Bool:
  match a b:
    case Con{x, xs} Con{y, ys}:
      bytes_eq(x, y) && path_eq(xs, ys)
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def path_str.go(ps: List<&2, List<&2, U32>>) -> String:
  match ps:
    case Con{p, rest}:
      "." ++ str(p) ++ path_str.go(rest)
    case Nil{}:
      ""

def path_str(ps: List<&2, List<&2, U32>>) -> String:
  match ps:
    case Con{p, rest}:
      str(p) ++ path_str.go(rest)
    case Nil{}:
      ""

def lay_show(+k: U32) -> String:
  match k:
    case 0:
      "the start of a layout group"
    case 1:
      "a new line of a layout group"
    case _:
      "the end of a layout group"

# a token named for a message
def tok_show(t: L.Tok) -> String:
  match t:
    case L.TWord{+line, +col, s}:
      str(s)
    case L.TDot{+line, +col}:
      "."
    case L.TEq{+line, +col}:
      "="
    case L.TText{+line, +col, s}:
      "a text"
    case L.TOpen{+line, +col}:
      "an unclosed text"
    case L.TOther{+line, +col, +b}:
      str([b])
    case L.TPun{+line, +col, +b}:
      str([b])
    case L.TOp{+line, +col, s}:
      str(s)
    case L.TLay{+line, +col, +k}:
      lay_show(k)

# Declarations
# ============
#
# Tokens grouped into declarations: a token at column 0 begins one, and
# the tokens after it, indented, continue it. A first token indented is
# an error (parse.first).

# the current declaration reversed, and the declarations before it
type Ga is Data:
  Ga{cur: List<&2, L.Tok>, gs: List<&2, List<&2, L.Tok>>}

def groups.put(cur: List<&2, L.Tok>, gs: List<&2, List<&2, L.Tok>>) -> List<&2, List<&2, L.Tok>>:
  match cur:
    case Nil{}:
      gs
    case Con{t, rest}:
      Con{List.reverse(&2, L.Tok, Con{t, rest}), gs}

def groups.step(+starts: Bool, t: L.Tok, a: Ga) -> Ga:
  match starts a:
    case True{} Ga{cur, gs}:
      Ga{[t], groups.put(cur, gs)}
    case False{} Ga{cur, gs}:
      Ga{Con{t, cur}, gs}

def groups.end(a: Ga) -> List<&2, List<&2, L.Tok>>:
  match a:
    case Ga{cur, gs}:
      List.reverse(&2, List<&2, L.Tok>, groups.put(cur, gs))

def groups.go(ts: List<&2, L.Tok>, a: Ga) -> List<&2, List<&2, L.Tok>>:
  match ts:
    case Con{+t, rest}:
      groups.go(rest, groups.step(U32.is_eq(L.tok_col(t), 0), t, a))
    case Nil{}:
      groups.end(a)

def groups(ts: List<&2, L.Tok>) -> List<&2, List<&2, L.Tok>>:
  groups.go(ts, Ga{Nil{}, Nil{}})

# The header
# ==========

type Hd is Data:
  HOk{+utf8: Bool}
  HErr{d: Diag}

def missing_language(+line: U32) -> Hd:
  HErr{Diag{line, "expected the language declaration first, `language g0`"}}

# the extensions after `with`, walked with whether `utf8` was among them
# and the first unknown one; `utf8` is the one known
def ext.bad(+known: Bool, bad: Maybe<&2, List<&2, U32>>, s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match known bad:
    case _ Some{b}:
      Some{b}
    case True{} None{}:
      None{}
    case False{} None{}:
      Some{s}

def exts.end(+line: U32, +utf8: Bool, bad: Maybe<&2, List<&2, U32>>) -> Hd:
  match bad:
    case Some{s}:
      HErr{Diag{line, "unrecognized language extension " ++ str(s)}}
    case None{}:
      HOk{utf8}

def exts(ts: List<&2, L.Tok>, +line: U32, +utf8: Bool, bad: Maybe<&2, List<&2, U32>>) -> Hd:
  match ts:
    case Nil{}:
      exts.end(line, utf8, bad)
    case Con{+t, rest}:
      match t:
        case L.TWord{+l, +c, +s}:
          exts(rest, line, utf8 || bytes_eq(s, [117, 116, 102, 56]), ext.bad(bytes_eq(s, [117, 116, 102, 56]), bad, s))
        case _:
          HErr{Diag{line, "expected an extension name after with, found " ++ tok_show(t)}}

# after `with`, at least one extension
def exts.some(ts: List<&2, L.Tok>, +line: U32) -> Hd:
  match ts:
    case Nil{}:
      HErr{Diag{line, "expected an extension name after with"}}
    case Con{t, rest}:
      exts(Con{t, rest}, line, False{}, None{})

def with.ok(+is_with: Bool, +line: U32, t: L.Tok, rest: List<&2, L.Tok>) -> Hd:
  match is_with:
    case True{}:
      exts.some(rest, line)
    case False{}:
      HErr{Diag{line, "expected with after the language version, found " ++ tok_show(t)}}

# after the version: nothing, or `with` and extensions
def after_version(ts: List<&2, L.Tok>, +line: U32) -> Hd:
  match ts:
    case Nil{}:
      HOk{False{}}
    case Con{+t, rest}:
      match t:
        case L.TWord{+l, +c, s}:
          with.ok(bytes_eq(s, [119, 105, 116, 104]), line, L.TWord{l, c, s}, rest)
        case _:
          HErr{Diag{line, "expected with after the language version, found " ++ tok_show(t)}}

def version.ok(+is_g0: Bool, +line: U32, s: List<&2, U32>, rest: List<&2, L.Tok>) -> Hd:
  match is_g0:
    case True{}:
      after_version(rest, line)
    case False{}:
      HErr{Diag{line, "unrecognized language version " ++ str(s)}}

# after `language`: the version
def version(ts: List<&2, L.Tok>, +line: U32) -> Hd:
  match ts:
    case Nil{}:
      HErr{Diag{line, "expected a language version after language"}}
    case Con{+t, rest}:
      match t:
        case L.TWord{+l, +c, s}:
          version.ok(bytes_eq(s, [103, 48]), line, s, rest)
        case _:
          HErr{Diag{line, "expected a language version after language, found " ++ tok_show(t)}}

def header.first(+is_language: Bool, +line: U32, rest: List<&2, L.Tok>) -> Hd:
  match is_language:
    case True{}:
      version(rest, line)
    case False{}:
      missing_language(line)

# the first declaration, which must be the language declaration
def header(g: List<&2, L.Tok>) -> Hd:
  match g:
    case Nil{}:
      missing_language(1)
    case Con{+t, rest}:
      match t:
        case L.TWord{+line, +col, s}:
          header.first(bytes_eq(s, [108, 97, 110, 103, 117, 97, 103, 101]), line, rest)
        case _:
          missing_language(L.tok_line(t))

# Definitions
# ===========

type Dc is Data:
  DOk{d: Def}
  DErr{d: Diag}

# a name begins with a letter
def name_ok(s: List<&2, U32>) -> Bool:
  match s:
    case Con{+b, rest}:
      L.is_letter(b)
    case Nil{}:
      False{}

# Expressions
# ===========
#
# One machine over a declaration's tokens after `=`, Bend admitting no
# mutual recursion for a parser that descends: a stack of open frames (a
# list's `[`, a `(`, an infix operator waiting for its right operand, a
# binding group and the binding being read, a `let`'s body) and the mode,
# an operand wanted or one in hand, or a binding group's own places.
# Precedence in glam is a partial relation (docs/Syntax.md, Operators): a
# chain of one operator needs no parentheses, two different ones do.
# `++` is the one known so far; its chains group to the right, append
# being associative. Binding groups come as glam/layout.bend makes them
# explicit: a virtual open, separators and close, or braces.

# a binding read: its line, its name, its value
type Bd is Data:
  Bd{+line: U32, name: List<&2, U32>, value: Expr}

type Fr is Data:
  # an open `[`: its line, the members so far reversed, and how it
  # stands: 0 just opened, 1 after a leading comma, 2 after a member's
  # comma
  FList{+line: U32, xs: List<&2, Expr>, +sep: U32}
  FParen{+line: U32}
  FOp{+line: U32, op: List<&2, U32>, a: Expr}
  # a binding group: 1 `let`'s or 2 `where`'s, its keyword's line, its
  # anchor's column, whether braces delimit it, the bindings so far
  # reversed, and for `where` the expression it scopes
  FGroup{+kind: U32, +line: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>, body: Expr}
  # a binding whose value is being read, and its parameters
  FBind{+line: U32, name: List<&2, U32>, ps: List<&2, List<&2, U32>>}
  # a `let`'s body being read, its group closed
  FLetBody{+line: U32, +anchor: U32, bs: List<&2, Bd>}
  # a function awaiting its argument: application by juxtaposition, the
  # tightest form after a name's path, grouping to the left
  FApp{+line: U32, f: Expr}
  # a lambda's body being read: its parameters in order
  FLam{+line: U32, ps: List<&2, List<&2, U32>>}

type Pm is Data:
  MWant{st: List<&2, Fr>}
  MHave{st: List<&2, Fr>, e: Expr}
  # after a name and `.`: the path so far
  MDot{st: List<&2, Fr>, +line: U32, path: List<&2, List<&2, U32>>}
  # after `let` or `where`: the group's open wanted
  MGroup{st: List<&2, Fr>}
  # a binding's name wanted, or the group's close
  MBName{st: List<&2, Fr>}
  # after a binding's name: its parameters so far reversed, then `=`
  MBEq{st: List<&2, Fr>, +line: U32, name: List<&2, U32>, ps: List<&2, List<&2, U32>>}
  # after `\`: a lambda's parameters so far reversed, then `->`
  MLam{st: List<&2, Fr>, +line: U32, ps: List<&2, List<&2, U32>>}
  # a `let` group closed: `in` or its body wanted
  MLetAfter{st: List<&2, Fr>, +line: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>}
  # a `where` group closed: nothing may follow but the end or a `)`
  MWhereDone{st: List<&2, Fr>, e: Expr, +anchor: U32}
  MFail{d: Diag}

type Ex is Data:
  XOk{e: Expr}
  XErr{d: Diag}

def fail(+line: U32, msg: String) -> Pm:
  MFail{Diag{line, msg}}

def no_right(+line: U32) -> Pm:
  fail(line, "an infix operator requires a right operand")

# a group's bindings, read in order, before the body they scope
def chain(bs: List<&2, Bd>, acc: Expr) -> Expr:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case Bd{+line, name, value}:
          chain(rest, EBind{line, name, value, acc})

# a body inside lambdas of the parameters, the first outermost
def lams(ps: List<&2, List<&2, U32>>, +line: U32, body: Expr) -> Expr:
  match ps:
    case Nil{}:
      body
    case Con{p, rest}:
      ELam{line, p, lams(rest, line, body)}

# Numbers: decimal digits, at most ten and below 2^32 for now, exact
# rationals coming with ladder-numbers; past that a diagnostic, never a
# Nat past 2^48, which would stop the program (AGENTS.md: a crash on user
# input is a bug).

def all_digits(s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+b, rest}:
      L.is_digit(b) && all_digits(rest)

def nat_of(s: List<&2, U32>, acc: Nat) -> Nat:
  match s:
    case Nil{}:
      acc
    case Con{+b, rest}:
      nat_of(rest, Nat.add(Nat.mul(acc, 10n), U32.to_nat((b - 48 : U32))))

def num.v(+small: Bool, st: List<&2, Fr>, +line: U32, +v: Nat) -> Pm:
  match small:
    case True{}:
      MHave{st, ENum{U32.from_nat(v)}}
    case False{}:
      fail(line, "a number past 2^32 - 1 is not supported yet")

def num.k(+ok: Bool, st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  match ok:
    case True{}:
      num.v(Nat.is_le(nat_of(s, 0n), 4294967295n), st, line, nat_of(s, 0n))
    case False{}:
      fail(line, "this number form is not supported yet: " ++ str(s))

def number(st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  num.k(all_digits(s) && Nat.is_le(List.length(&2, U32, s), 10n), st, line, s)

def word_kind.k(+digit: Bool, +letter: Bool) -> U32:
  match digit letter:
    case True{} _:
      1
    case False{} True{}:
      2
    case False{} False{}:
      0

# a word's first byte: 1 a digit, 2 a letter, 0 anything else
def word_kind(s: List<&2, U32>) -> U32:
  match s:
    case Con{+b, rest}:
      word_kind.k(L.is_digit(b), L.is_letter(b))
    case Nil{}:
      0

# a name where an operand is wanted: `let` opens a group; `in` and
# `where` belong after one
def name.k(+kw: U32, st: List<&2, Fr>, +line: U32, s: List<&2, U32>) -> Pm:
  match kw:
    case 2:
      MGroup{Con{FGroup{1, line, 0, False{}, Nil{}, ENum{0}}, st}}
    case 1:
      fail(line, "expected an expression, found in")
    case 3:
      fail(line, "expected an expression, found where")
    case _:
      MHave{st, EName{line, [s]}}

def word.k(+kind: U32, st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  match kind:
    case 1:
      number(st, line, s)
    case 2:
      name.k(Y.word_part(s), st, line, s)
    case _:
      fail(line, "this form is not supported yet: " ++ str(s))

def word(st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  word.k(word_kind(s), st, line, s)

# Closers and commas where an operand is wanted
# ---------------------------------------------

def mismatch(+line: U32, want: String, +b: U32) -> Pm:
  fail(line, "mismatched closing delimiter: expected `" ++ want ++ "`, found `" ++ str([b]) ++ "`")

# `]` or `)` facing an open `[`: an empty list, a trailing comma's end, or
# an empty member after a lone leading comma
def want.close.list(+sq: Bool, +sep: U32, xs: List<&2, Expr>, rest: List<&2, Fr>, +line: U32, +b: U32) -> Pm:
  match sq sep:
    case False{} _:
      mismatch(line, "]", b)
    case True{} 1:
      fail(line, "a list holds an empty member between separators")
    case True{} _:
      MHave{rest, EList{List.reverse(&2, Expr, xs)}}

def want.close.paren(+round: Bool, +line: U32, +b: U32) -> Pm:
  match round:
    case True{}:
      fail(line, "this form is not supported yet: ()")
    case False{}:
      mismatch(line, ")", b)

def want.close(st: List<&2, Fr>, +line: U32, +b: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "unbalanced closing delimiter `" ++ str([b]) ++ "`")
    case Con{f, rest}:
      match f:
        case FList{+l, xs, +sep}:
          want.close.list(U32.is_eq(b, 93), sep, xs, rest, line, b)
        case FParen{+l}:
          want.close.paren(U32.is_eq(b, 41), line, b)
        case FOp{+l, op, a}:
          no_right(l)
        case _:
          fail(line, "expected an expression before `" ++ str([b]) ++ "`")

def want.comma.k(+sep: U32, +l: U32, xs: List<&2, Expr>, rest: List<&2, Fr>, +line: U32) -> Pm:
  match sep:
    case 0:
      MWant{Con{FList{l, xs, 1}, rest}}
    case _:
      fail(line, "a list holds an empty member between separators")

def want.comma(st: List<&2, Fr>, +line: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "a comma outside brackets")
    case Con{f, rest}:
      match f:
        case FList{+l, xs, +sep}:
          want.comma.k(sep, l, xs, rest, line)
        case FParen{+l}:
          fail(line, "tuples are not supported yet")
        case FOp{+l, op, a}:
          no_right(l)
        case _:
          fail(line, "expected an expression before `,`")

def want.pun(st: List<&2, Fr>, +line: U32, +b: U32) -> Pm:
  match b:
    case 91:
      MWant{Con{FList{line, Nil{}, 0}, st}}
    case 40:
      MWant{Con{FParen{line}, st}}
    case 93:
      want.close(st, line, 93)
    case 41:
      want.close(st, line, 41)
    case 44:
      want.comma(st, line)
    case _:
      fail(line, "this form is not supported yet: " ++ str([b]))

# an operator where an operand is wanted: `\` begins a lambda
def want.op(+lam: Bool, st: List<&2, Fr>, +line: U32, s: List<&2, U32>) -> Pm:
  match lam:
    case True{}:
      MLam{st, line, Nil{}}
    case False{}:
      fail(line, "expected an expression before " ++ str(s))

# an operand wanted
def want(st: List<&2, Fr>, t: L.Tok) -> Pm:
  match t:
    case L.TText{+l, +c, s}:
      MHave{st, EText{s}}
    case L.TOpen{+l, +c}:
      fail(l, "a text is not closed on its line")
    case L.TWord{+l, +c, s}:
      word(st, l, s)
    case L.TPun{+l, +c, +b}:
      want.pun(st, l, b)
    case L.TOp{+l, +c, +s}:
      want.op(bytes_eq(s, [92]), st, l, s)
    case L.TEq{+l, +c}:
      fail(l, "expected an expression, found =")
    case L.TDot{+l, +c}:
      fail(l, "expected an expression, found .")
    case L.TOther{+l, +c, +b}:
      fail(l, "unexpected character " ++ str([b]))
    case L.TLay{+l, +c, +k}:
      fail(l, "expected an expression")

# Operators, commas and closers after an operand
# ----------------------------------------------

type Rd is Data:
  Rd{st: List<&2, Fr>, e: Expr}

# the frames that end where their expression ends applied, the latest
# first: an operator waiting, so that a chain of one operator groups to
# the right, and a `let`'s body, a tail form (tail-forms-end-at-separators)
def reduce(st: List<&2, Fr>, e: Expr) -> Rd:
  match st:
    case Nil{}:
      Rd{Nil{}, e}
    case Con{f, rest}:
      match f:
        case FOp{+line, op, a}:
          reduce(rest, EOp2{line, op, a, e})
        case FLetBody{+line, +anchor, bs}:
          reduce(rest, ELet{line, chain(bs, EIn{e})})
        case FApp{+line, g}:
          reduce(rest, EApp{line, g, e})
        case FLam{+line, ps}:
          reduce(rest, lams(ps, line, e))
        case _:
          Rd{Con{f, rest}, e}

def have.op.k(+known: Bool, st: List<&2, Fr>, e: Expr, +line: U32, op: List<&2, U32>) -> Pm:
  match known:
    case True{}:
      MWant{Con{FOp{line, op, e}, st}}
    case False{}:
      fail(line, "the operator " ++ str(op) ++ " is not supported yet")

def have.op(st: List<&2, Fr>, e: Expr, +line: U32, +op: List<&2, U32>) -> Pm:
  have.op.k(bytes_eq(op, [43, 43]), st, e, line, op)

def unclosed.pm(f: Fr) -> Pm:
  match f:
    case FList{+l, xs, +sep}:
      fail(l, "unclosed delimiter: expected `]`")
    case FParen{+l}:
      fail(l, "unclosed delimiter: expected `)`")
    case _:
      fail(0, "an expression ended where its frame does not")

def have.comma(r: Rd, +line: U32) -> Pm:
  match r:
    case Rd{st, e}:
      match st:
        case Nil{}:
          fail(line, "a comma outside brackets")
        case Con{f, rest}:
          match f:
            case FList{+l, xs, +sep}:
              MWant{Con{FList{l, Con{e, xs}, 2}, rest}}
            case FParen{+l}:
              fail(line, "tuples are not supported yet")
            case _:
              fail(line, "a comma outside brackets")

def have.close.list(+sq: Bool, xs: List<&2, Expr>, e: Expr, rest: List<&2, Fr>, +line: U32, +b: U32) -> Pm:
  match sq:
    case True{}:
      MHave{rest, EList{List.reverse(&2, Expr, Con{e, xs})}}
    case False{}:
      mismatch(line, "]", b)

def have.close.paren(+round: Bool, e: Expr, rest: List<&2, Fr>, +line: U32, +b: U32) -> Pm:
  match round:
    case True{}:
      MHave{rest, e}
    case False{}:
      mismatch(line, ")", b)

def have.close(r: Rd, +line: U32, +b: U32) -> Pm:
  match r:
    case Rd{st, e}:
      match st:
        case Nil{}:
          fail(line, "unbalanced closing delimiter `" ++ str([b]) ++ "`")
        case Con{f, rest}:
          match f:
            case FList{+l, xs, +sep}:
              have.close.list(U32.is_eq(b, 93), xs, e, rest, line, b)
            case FParen{+l}:
              have.close.paren(U32.is_eq(b, 41), e, rest, line, b)
            case _:
              fail(line, "unbalanced closing delimiter `" ++ str([b]) ++ "`")

# Binding groups
# --------------

def group_word(+kind: U32) -> String:
  match kind:
    case 1:
      "let"
    case _:
      "where"

def naked(+kind: U32, +line: U32) -> Pm:
  match kind:
    case 1:
      fail(line, "naked semicolon-separated `let` bindings: use `let { ... } in ...`")
    case _:
      fail(line, "naked semicolon-separated `where` bindings: use `where { ... }`")

# a group closed: a `let`'s body comes next, a `where` scopes its body
def group_close(+kind: U32, +line: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>, body: Expr, rest: List<&2, Fr>) -> Pm:
  match kind:
    case 1:
      MLetAfter{rest, line, anchor, brace, bs}
    case _:
      MWhereDone{rest, ELet{line, chain(bs, EIn{body})}, anchor}

# after a binding, or where a binding's name is wanted: how the group
# goes on, by what came (1 a virtual separator, 2 a virtual close, 3 a
# `;`, 4 a `}`) and whether braces delimit it
def group_next(+how: U32, +kind: U32, +gl: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>, body: Expr, rest: List<&2, Fr>, +line: U32) -> Pm:
  match how brace:
    case 1 False{}:
      MBName{Con{FGroup{kind, gl, anchor, brace, bs, body}, rest}}
    case 2 False{}:
      group_close(kind, gl, anchor, brace, bs, body, rest)
    case 3 False{}:
      naked(kind, line)
    case 3 True{}:
      MBName{Con{FGroup{kind, gl, anchor, brace, bs, body}, rest}}
    case 4 True{}:
      group_close(kind, gl, anchor, brace, bs, body, rest)
    case _ _:
      fail(line, "a `" ++ group_word(kind) ++ "` group's bindings end in a mismatched delimiter")

def bind_add(st: List<&2, Fr>, b: Bd, +how: U32, +line: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "a binding outside its group")
    case Con{g, rest}:
      match g:
        case FGroup{+kind, +gl, +anchor, +brace, bs, body}:
          group_next(how, kind, gl, anchor, brace, Con{b, bs}, body, rest, line)
        case _:
          fail(line, "a binding outside its group")

# a binding's value ended by a separator or the group's close
def bind_end(r: Rd, +how: U32, +line: U32) -> Pm:
  match r:
    case Rd{st, e}:
      match st:
        case Nil{}:
          fail(line, "a separator outside a binding group")
        case Con{f, rest}:
          match f:
            case FBind{+bl, name, ps}:
              bind_add(rest, Bd{bl, name, lams(ps, bl, e)}, how, line)
            case FList{+l, xs, +sep}:
              fail(l, "unclosed delimiter: expected `]`")
            case FParen{+l}:
              fail(l, "unclosed delimiter: expected `)`")
            case _:
              fail(line, "a separator outside a binding group")

# where a binding's name is wanted, the group's frame on top: the group
# goes on or closes by what came
def name_next(st: List<&2, Fr>, +how: U32, +line: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "a binding group's frame lost")
    case Con{g, rest}:
      match g:
        case FGroup{+kind, +gl, +anchor, +brace, bs, body}:
          group_next(how, kind, gl, anchor, brace, bs, body, rest, line)
        case _:
          fail(line, "a binding group's frame lost")

# `where` after an operand: it scopes the whole definition, binding or
# parenthesized expression it ends, the open tails before it ended
def where_start(r: Rd, +line: U32) -> Pm:
  match r:
    case Rd{st, e}:
      match st:
        case Nil{}:
          MGroup{[FGroup{2, line, 0, False{}, Nil{}, e}]}
        case Con{f, rest}:
          match f:
            case FList{+l, xs, +sep}:
              fail(line, "a `where` inside a list: write `(e where ...)`")
            case _:
              MGroup{Con{FGroup{2, line, 0, False{}, Nil{}, e}, Con{f, rest}}}

def have.word.k(+kw: U32, st: List<&2, Fr>, e: Expr, +line: U32, +col: U32, s: List<&2, U32>) -> Pm:
  match kw:
    case 3:
      where_start(reduce(st, e), line)
    case 1:
      fail(line, "unexpected in")
    case 2:
      fail(line, "a `let` as an argument: write `(let ...)`")
    case _:
      want(Con{FApp{line, e}, st}, L.TWord{line, col, s})

# a word after an operand: `where`, or an argument
def have.word(st: List<&2, Fr>, e: Expr, +line: U32, +col: U32, +s: List<&2, U32>) -> Pm:
  have.word.k(Y.word_part(s), st, e, line, col, s)

def have.pun(st: List<&2, Fr>, e: Expr, +line: U32, +b: U32) -> Pm:
  match b:
    case 44:
      have.comma(reduce(st, e), line)
    case 93:
      have.close(reduce(st, e), line, 93)
    case 41:
      have.close(reduce(st, e), line, 41)
    case 59:
      bind_end(reduce(st, e), 3, line)
    case 125:
      bind_end(reduce(st, e), 4, line)
    case 91:
      want.pun(Con{FApp{line, e}, st}, line, 91)
    case 40:
      want.pun(Con{FApp{line, e}, st}, line, 40)
    case _:
      fail(line, "this form is not supported yet: " ++ str([b]))

# `=` after an operand: a binding left of its group's anchor, where a
# `let`'s body has just begun
def have.eq(st: List<&2, Fr>, +line: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "unexpected =")
    case Con{f, rest}:
      match f:
        case FLetBody{+l, +anchor, bs}:
          fail(line, "multi-line let binding: expected sibling indentation " ++ U32.show(anchor))
        case _:
          fail(line, "unexpected =")

# `.` after an operand: a path goes on after a name
def have.dot(e: Expr, st: List<&2, Fr>, +line: U32) -> Pm:
  match e:
    case EName{+l, path}:
      MDot{st, l, path}
    case _:
      fail(line, "a field of an expression is not supported yet")

# an operand in hand, its application done
def have.t(st: List<&2, Fr>, e: Expr, t: L.Tok) -> Pm:
  match t:
    case L.TOp{+l, +c, s}:
      have.op(st, e, l, s)
    case L.TPun{+l, +c, +b}:
      have.pun(st, e, l, b)
    case L.TDot{+l, +c}:
      have.dot(e, st, l)
    case L.TWord{+l, +c, s}:
      have.word(st, e, l, c, s)
    case L.TText{+l, +c, s}:
      want(Con{FApp{l, e}, st}, L.TText{l, c, s})
    case L.TOpen{+l, +c}:
      fail(l, "a text is not closed on its line")
    case L.TEq{+l, +c}:
      have.eq(st, l)
    case L.TOther{+l, +c, +b}:
      fail(l, "unexpected character " ++ str([b]))
    case L.TLay{+l, +c, +k}:
      bind_end(reduce(st, e), k, l)

def is_dot(t: L.Tok) -> Bool:
  match t:
    case L.TDot{+l, +c}:
      True{}
    case _:
      False{}

def have.app.if(more: Unit -> Pm, +dot: Bool, +l: U32, f: Expr, rest: List<&2, Fr>, e: Expr, t: L.Tok) -> Pm:
  match dot:
    case True{}:
      have.t(Con{FApp{l, f}, rest}, e, t)
    case False{}:
      more(Unit{})

# an operand in hand: the application awaiting it done first, unless a
# name's path goes on
def have(st: List<&2, Fr>, +e: Expr, +t: L.Tok) -> Pm:
  match st:
    case Nil{}:
      have.t(Nil{}, e, t)
    case Con{f, +rest}:
      match f:
        case FApp{+l, +g}:
          have.app.if(u => have(rest, EApp{l, g, e}, t), is_dot(t), l, g, rest, e, t)
        case _:
          have.t(Con{f, rest}, e, t)

def dot.word(+ok: Bool, st: List<&2, Fr>, +line: U32, path: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Pm:
  match ok:
    case True{}:
      MHave{st, EName{line, List.append(&2, List<&2, U32>, path, [s])}}
    case False{}:
      fail(line, "expected a name after .")

# after `name.`: the path's next name
def dot(st: List<&2, Fr>, +line: U32, path: List<&2, List<&2, U32>>, t: L.Tok) -> Pm:
  match t:
    case L.TWord{+l, +c, +s}:
      dot.word(name_ok(s), st, line, path, s)
    case _:
      fail(line, "expected a name after .")

# the group's frame given its open: braces, or a virtual open at its
# anchor's column
def opened(st: List<&2, Fr>, +anchor: U32, +brace: Bool, +line: U32) -> Pm:
  match st:
    case Nil{}:
      fail(line, "a binding group's frame lost")
    case Con{g, rest}:
      match g:
        case FGroup{+kind, +gl, +a, +b, bs, body}:
          MBName{Con{FGroup{kind, gl, anchor, brace, bs, body}, rest}}
        case _:
          fail(line, "a binding group's frame lost")

def group.brace(+brace: Bool, st: List<&2, Fr>, +line: U32) -> Pm:
  match brace:
    case True{}:
      opened(st, 0, True{}, line)
    case False{}:
      fail(line, "expected a binding group")

def group(st: List<&2, Fr>, +t: L.Tok) -> Pm:
  match t:
    case L.TLay{+l, +c, +k}:
      opened(st, c, False{}, l)
    case L.TPun{+l, +c, +b}:
      group.brace(U32.is_eq(b, 123), st, l)
    case _:
      fail(L.tok_line(t), "expected a binding group, found " ++ tok_show(t))

def bname.kw(+kw: U32, st: List<&2, Fr>, +line: U32, s: List<&2, U32>) -> Pm:
  match kw:
    case 0:
      MBEq{st, line, s, Nil{}}
    case _:
      fail(line, "a keyword cannot name a binding: " ++ str(s))

def bname.k(+kind: U32, st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  match kind:
    case 2:
      bname.kw(Y.word_part(s), st, line, s)
    case _:
      fail(line, "a binding's name begins with a letter: " ++ str(s))

def bname.pun(+b: U32, st: List<&2, Fr>, +line: U32) -> Pm:
  match b:
    case 59:
      name_next(st, 3, line)
    case 125:
      name_next(st, 4, line)
    case _:
      fail(line, "expected a binding's name, found " ++ str([b]))

# a binding's name wanted, or the group's close
def bname(st: List<&2, Fr>, +t: L.Tok) -> Pm:
  match t:
    case L.TWord{+l, +c, +s}:
      bname.k(word_kind(s), st, l, s)
    case L.TLay{+l, +c, +k}:
      name_next(st, k, l)
    case L.TPun{+l, +c, +b}:
      bname.pun(b, st, l)
    case _:
      fail(L.tok_line(t), "expected a binding's name, found " ++ tok_show(t))

# a parameter's name: a word beginning with a letter, no keyword
def param_ok(+s: List<&2, U32>) -> Bool:
  name_ok(s) && U32.is_eq(Y.word_part(s), 0)

def beq.p(+ok: Bool, st: List<&2, Fr>, +line: U32, name: List<&2, U32>, ps: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Pm:
  match ok:
    case True{}:
      MBEq{st, line, name, Con{s, ps}}
    case False{}:
      fail(line, "a parameter's name begins with a letter and is no keyword: " ++ str(s))

# after a binding's name: its parameters, then `=`, its value's frame
# pushed
def beq(st: List<&2, Fr>, +line: U32, name: List<&2, U32>, ps: List<&2, List<&2, U32>>, +t: L.Tok) -> Pm:
  match t:
    case L.TEq{+l, +c}:
      MWant{Con{FBind{line, name, List.reverse(&2, List<&2, U32>, ps)}, st}}
    case L.TWord{+l, +c, +s}:
      beq.p(param_ok(s), st, line, name, ps, s)
    case _:
      fail(line, "expected = after the binding's name, found " ++ tok_show(t))

def lam.p(+ok: Bool, st: List<&2, Fr>, +line: U32, ps: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Pm:
  match ok:
    case True{}:
      MLam{st, line, Con{s, ps}}
    case False{}:
      fail(line, "a parameter's name begins with a letter and is no keyword: " ++ str(s))

def lam.arrow(+arrow: Bool, st: List<&2, Fr>, +line: U32, ps: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Pm:
  match arrow ps:
    case True{} Nil{}:
      fail(line, "a lambda needs a parameter before ->")
    case True{} Con{p, rest}:
      MWant{Con{FLam{line, List.reverse(&2, List<&2, U32>, Con{p, rest})}, st}}
    case False{} _:
      fail(line, "expected a parameter or -> in a lambda, found " ++ str(s))

# after `\`: the lambda's parameters, then `->`, its body's frame pushed
def lam_params(st: List<&2, Fr>, +line: U32, ps: List<&2, List<&2, U32>>, +t: L.Tok) -> Pm:
  match t:
    case L.TWord{+l, +c, +s}:
      lam.p(param_ok(s), st, line, ps, s)
    case L.TOp{+l, +c, +s}:
      lam.arrow(bytes_eq(s, [45, 62]), st, line, ps, s)
    case _:
      fail(line, "expected a parameter or -> in a lambda, found " ++ tok_show(t))

def let_in(+same: Bool, +brace: Bool, st: List<&2, Fr>, +line: U32, +anchor: U32, bs: List<&2, Bd>) -> Pm:
  match same brace:
    case False{} False{}:
      fail(line, "a multi-line let expression must not use `in`")
    case _ _:
      MWant{Con{FLetBody{line, anchor, bs}, st}}

# a `let` group closed: `in`, on the `let`'s line unless braces delimit
# the group, or its body directly (Local Definitions)
def let_after.k(+is_in: Bool, st: List<&2, Fr>, +line: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>, +t: L.Tok) -> Pm:
  match is_in:
    case True{}:
      let_in(U32.is_eq(L.tok_line(t), line), brace, st, line, anchor, bs)
    case False{}:
      want(Con{FLetBody{line, anchor, bs}, st}, t)

def let_after(st: List<&2, Fr>, +line: U32, +anchor: U32, +brace: Bool, bs: List<&2, Bd>, +t: L.Tok) -> Pm:
  let_after.k(Y.is_in(t), st, line, anchor, brace, bs, t)

def where_done.pun(+close: Bool, st: List<&2, Fr>, e: Expr, +line: U32, +b: U32) -> Pm:
  match close:
    case True{}:
      have.close(reduce(st, e), line, b)
    case False{}:
      fail(line, "nothing may follow a where's bindings")

def where_done(st: List<&2, Fr>, e: Expr, +anchor: U32, t: L.Tok) -> Pm:
  match t:
    case L.TPun{+l, +c, +b}:
      where_done.pun(U32.is_eq(b, 41), st, e, l, b)
    case L.TWord{+l, +c, s}:
      fail(l, "multi-line where binding: expected sibling indentation " ++ U32.show(anchor))
    case _:
      fail(L.tok_line(t), "nothing may follow a where's bindings")

def step(m: Pm, +t: L.Tok) -> Pm:
  match m:
    case MFail{d}:
      MFail{d}
    case MWant{st}:
      want(st, t)
    case MHave{st, e}:
      have(st, e, t)
    case MDot{st, +line, path}:
      dot(st, line, path, t)
    case MGroup{st}:
      group(st, t)
    case MBName{st}:
      bname(st, t)
    case MBEq{st, +line, name, ps}:
      beq(st, line, name, ps, t)
    case MLam{st, +line, ps}:
      lam_params(st, line, ps, t)
    case MLetAfter{st, +line, +anchor, +brace, bs}:
      let_after(st, line, anchor, brace, bs, t)
    case MWhereDone{st, e, +anchor}:
      where_done(st, e, anchor, t)

def expr.go(ts: List<&2, L.Tok>, m: Pm) -> Pm:
  match ts:
    case Nil{}:
      m
    case Con{t, rest}:
      expr.go(rest, step(m, t))

# The end of a declaration
# ------------------------

def unclosed(f: Fr) -> Ex:
  match f:
    case FList{+l, xs, +sep}:
      XErr{Diag{l, "unclosed delimiter: expected `]`"}}
    case FParen{+l}:
      XErr{Diag{l, "unclosed delimiter: expected `)`"}}
    case FOp{+l, op, a}:
      XErr{Diag{l, "an infix operator requires a right operand"}}
    case FGroup{+kind, +l, +anchor, +brace, bs, body}:
      XErr{Diag{l, "a `" ++ group_word(kind) ++ "` group is not closed"}}
    case FBind{+l, name, ps}:
      XErr{Diag{l, "a binding's value is missing"}}
    case FLetBody{+l, +anchor, bs}:
      XErr{Diag{l, "a `let`'s body is missing"}}
    case FApp{+l, f}:
      XErr{Diag{l, "an application's argument is missing"}}
    case FLam{+l, ps}:
      XErr{Diag{l, "a lambda's body is missing"}}

def end.want(st: List<&2, Fr>, +line: U32) -> Ex:
  match st:
    case Nil{}:
      XErr{Diag{line, "expected an expression after ="}}
    case Con{f, rest}:
      unclosed(f)

def end.have(r: Rd) -> Ex:
  match r:
    case Rd{st, e}:
      match st:
        case Nil{}:
          XOk{e}
        case Con{f, rest}:
          unclosed(f)

def end(m: Pm, +line: U32) -> Ex:
  match m:
    case MFail{d}:
      XErr{d}
    case MDot{st, +l, path}:
      XErr{Diag{l, "expected a name after ."}}
    case MWant{st}:
      end.want(st, line)
    case MHave{st, e}:
      end.have(reduce(st, e))
    case MWhereDone{st, e, +anchor}:
      end.have(reduce(st, e))
    case MLetAfter{st, +l, +anchor, +brace, bs}:
      XErr{Diag{l, "a `let`'s body is missing"}}
    case MGroup{st}:
      XErr{Diag{line, "expected a binding group"}}
    case MBName{st}:
      XErr{Diag{line, "a binding group is not closed"}}
    case MBEq{st, +l, name, ps}:
      XErr{Diag{l, "expected = after the binding's name"}}
    case MLam{st, +l, ps}:
      XErr{Diag{l, "a lambda is not finished: expected ->"}}

def body.x(x: Ex, +line: U32, path: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>) -> Dc:
  match x:
    case XOk{e}:
      DOk{Def{line, path, lams(ps, line, e)}}
    case XErr{d}:
      DErr{d}

# the body after `=`: an expression, to the declaration's end, inside
# lambdas of the definition's parameters
def body(ts: List<&2, L.Tok>, +line: U32, path: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>) -> Dc:
  body.x(end(expr.go(ts, MWant{Nil{}}), line), line, path, ps)

# a path being read: the names so far reversed and whether a name is
# expected next (after `.`, or at the start) or `.` or `=`; then the body
# begins, or the declaration failed
type Ps is Data:
  PNext{acc: List<&2, List<&2, U32>>, +name: Bool}
  # after the path, its parameters so far reversed
  PParams{acc: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>}
  PBody{path: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>}
  PFail{d: Diag}

def path.word(+ok: Bool, +line: U32, s: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> Ps:
  match ok:
    case True{}:
      PNext{Con{s, acc}, False{}}
    case False{}:
      PFail{Diag{line, "a name begins with a letter: " ++ str(s)}}

# a token's kind for the path: 1 a word, 2 a dot, 3 an equals sign, 0 else
def tok_kind(t: L.Tok) -> U32:
  match t:
    case L.TWord{+line, +col, s}:
      1
    case L.TDot{+line, +col}:
      2
    case L.TEq{+line, +col}:
      3
    case _:
      0

# a word's bytes; none for any other token
def tok_word(t: L.Tok) -> List<&2, U32>:
  match t:
    case L.TWord{+line, +col, s}:
      s
    case _:
      Nil{}

def path.param(+ok: Bool, +line: U32, s: List<&2, U32>, acc: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>) -> Ps:
  match ok:
    case True{}:
      PParams{acc, Con{s, ps}}
    case False{}:
      PFail{Diag{line, "a parameter's name begins with a letter and is no keyword: " ++ str(s)}}

# a token after the path's parameters: another, or `=`
def param.step.k(+kind: U32, +s: List<&2, U32>, shown: String, +line: U32, acc: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>) -> Ps:
  match kind:
    case 1:
      path.param(param_ok(s), line, s, acc, ps)
    case 3:
      PBody{List.reverse(&2, List<&2, U32>, acc), List.reverse(&2, List<&2, U32>, ps)}
    case _:
      PFail{Diag{line, "expected a parameter or = after the name, found " ++ shown}}

def param.step(+t: L.Tok, +line: U32, acc: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>) -> Ps:
  param.step.k(tok_kind(t), tok_word(t), tok_show(t), line, acc, ps)

# one token of a path, by its kind, a name expected or not
def path.step.k(+kind: U32, +s: List<&2, U32>, shown: String, +line: U32, acc: List<&2, List<&2, U32>>, +name: Bool) -> Ps:
  match kind name:
    case 1 True{}:
      path.word(name_ok(s), line, s, acc)
    case 1 False{}:
      path.param(param_ok(s), line, s, acc, Nil{})
    case 2 False{}:
      PNext{acc, True{}}
    case 3 False{}:
      PBody{List.reverse(&2, List<&2, U32>, acc), Nil{}}
    case _ True{}:
      PFail{Diag{line, "expected a name, found " ++ shown}}
    case _ False{}:
      PFail{Diag{line, "expected = after the name, found " ++ shown}}

def path.step(+t: L.Tok, +line: U32, acc: List<&2, List<&2, U32>>, +name: Bool) -> Ps:
  path.step.k(tok_kind(t), tok_word(t), tok_show(t), line, acc, name)

# the tokens ran out in the path
def path.end(+name: Bool, +line: U32) -> Dc:
  match name:
    case True{}:
      DErr{Diag{line, "expected a name after ."}}
    case False{}:
      DErr{Diag{line, "expected = after the name"}}

# the tokens first, so that the recursion shrinks them; the path's state
# beside them
def path.go(ts: List<&2, L.Tok>, st: Ps, +line: U32) -> Dc:
  match ts:
    case Con{t, rest}:
      match st:
        case PNext{acc, +name}:
          path.go(rest, path.step(t, line, acc, name), line)
        case PParams{acc, ps}:
          path.go(rest, param.step(t, line, acc, ps), line)
        case PBody{path, ps}:
          body(Con{t, rest}, line, path, ps)
        case PFail{d}:
          DErr{d}
    case Nil{}:
      match st:
        case PNext{acc, +name}:
          path.end(name, line)
        case PParams{acc, ps}:
          DErr{Diag{line, "expected = after the parameters"}}
        case PBody{path, ps}:
          body(Nil{}, line, path, ps)
        case PFail{d}:
          DErr{d}

def decl(g: List<&2, L.Tok>) -> Dc:
  match g:
    case Nil{}:
      DErr{Diag{0, "an empty declaration"}}
    case Con{+t, rest}:
      path.go(Y.layout(Con{t, rest}), PNext{Nil{}, True{}}, L.tok_line(t))

# the definitions and the diagnostics so far, each reversed
type Da is Data:
  Da{ds: List<&2, Def>, es: List<&2, Diag>}

def decls.put(r: Dc, a: Da) -> Da:
  match r a:
    case DOk{d} Da{ds, es}:
      Da{Con{d, ds}, es}
    case DErr{e} Da{ds, es}:
      Da{ds, Con{e, es}}

# every declaration after the header read
def decls(gs: List<&2, List<&2, L.Tok>>, a: Da) -> Da:
  match gs:
    case Nil{}:
      a
    case Con{g, rest}:
      decls(rest, decls.put(decl(g), a))

# a path defined twice: `=` introduces, and refuses what is defined
def dups.in(+p: List<&2, List<&2, U32>>, ds: List<&2, Def>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{e, rest}:
      match e:
        case Def{+l2, p2, b2}:
          path_eq(p, p2) || dups.in(p, rest)

# the definitions seen, and the diagnostics so far reversed
type Du is Data:
  Du{seen: List<&2, Def>, es: List<&2, Diag>}

def dups.put(+dup: Bool, d: Def, a: Du) -> Du:
  match dup d a:
    case True{} Def{+line, path, body} Du{seen, es}:
      Du{seen, Con{Diag{line, path_str(path) ++ " is already defined; := overrides"}, es}}
    case False{} Def{+line, path, body} Du{seen, es}:
      Du{Con{Def{line, path, body}, seen}, es}

def dups.step(d: Def, a: Du) -> Du:
  match d a:
    case Def{+line, +path, body} Du{+seen, es}:
      dups.put(dups.in(path, seen), Def{line, path, body}, Du{seen, es})

def dups.go(ds: List<&2, Def>, a: Du) -> List<&2, Diag>:
  match ds:
    case Nil{}:
      match a:
        case Du{seen, es}:
          List.reverse(&2, Diag, es)
    case Con{d, rest}:
      dups.go(rest, dups.step(d, a))

def dups(ds: List<&2, Def>) -> List<&2, Diag>:
  dups.go(ds, Du{Nil{}, Nil{}})

# The module
# ==========

def na_diag.k(+fine: Bool, +na: U32) -> List<&2, Diag>:
  match fine:
    case True{}:
      Nil{}
    case False{}:
      [Diag{na, "a non-ASCII byte: only `language g0 with utf8` admits one"}]

def na_diag(+na: U32, +utf8: Bool) -> List<&2, Diag>:
  na_diag.k(U32.is_eq(na, 0) || utf8, na)

def finish.k(es: List<&2, Diag>, +utf8: Bool, ds: List<&2, Def>) -> Parsed:
  match es:
    case Nil{}:
      POk{Mod{utf8, ds}}
    case Con{e, rest}:
      PErr{Con{e, rest}}

def finish(+utf8: Bool, a: Da, na: List<&2, Diag>) -> Parsed:
  match a:
    case Da{+ds, es}:
      finish.k(List.append(&2, Diag, na, List.append(&2, Diag, List.reverse(&2, Diag, es), dups(List.reverse(&2, Def, ds)))), utf8, List.reverse(&2, Def, ds))

def parse.hd(h: Hd, rest: List<&2, List<&2, L.Tok>>, +na: U32) -> Parsed:
  match h:
    case HErr{d}:
      PErr{[d]}
    case HOk{+utf8}:
      finish(utf8, decls(rest, Da{Nil{}, Nil{}}), na_diag(na, utf8))

def parse.gs(gs: List<&2, List<&2, L.Tok>>, +na: U32) -> Parsed:
  match gs:
    case Nil{}:
      PErr{[Diag{1, "expected the language declaration first, `language g0`"}]}
    case Con{g, rest}:
      parse.hd(header(g), rest, na)

def parse.first.k(+ok: Bool, ts: List<&2, L.Tok>, +na: U32) -> Parsed:
  match ok:
    case True{}:
      parse.gs(groups(ts), na)
    case False{}:
      match ts:
        case Con{+t, rest}:
          PErr{[Diag{L.tok_line(t), "expected a declaration at column 0, found " ++ tok_show(t)}]}
        case Nil{}:
          parse.gs(Nil{}, na)

# the first token must stand at column 0
def parse.first(ts: List<&2, L.Tok>, +na: U32) -> Parsed:
  match ts:
    case Con{+t, rest}:
      parse.first.k(U32.is_eq(L.tok_col(t), 0), Con{t, rest}, na)
    case Nil{}:
      parse.gs(Nil{}, na)

def parse(lx: L.Lx) -> Parsed:
  match lx:
    case L.Lx{toks, +na}:
      parse.first(toks, na)
