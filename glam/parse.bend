import Base
import ./lex.bend as L

# The ".g" parser, as far as the hello ladder has climbed (HelloLadder,
# ladder-text): the language declaration first (docs/Syntax.md, Language
# Version Declaration), then definitions `path = Expr`, each declaration
# beginning at column 0 and continuing on indented lines (Toplevel
# Structure). Expressions, as far as the ladder reaches: texts, decimal
# numbers, names and dotted paths, list literals, parentheses, and the
# infix `++` (ladder-lists). Diagnostics carry the line of the token at
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

def tok_line(t: L.Tok) -> U32:
  match t:
    case L.TWord{+line, +col, s}:
      line
    case L.TDot{+line, +col}:
      line
    case L.TEq{+line, +col}:
      line
    case L.TText{+line, +col, s}:
      line
    case L.TOpen{+line, +col}:
      line
    case L.TOther{+line, +col, +b}:
      line
    case L.TPun{+line, +col, +b}:
      line
    case L.TOp{+line, +col, s}:
      line

def tok_col(t: L.Tok) -> U32:
  match t:
    case L.TWord{+line, +col, s}:
      col
    case L.TDot{+line, +col}:
      col
    case L.TEq{+line, +col}:
      col
    case L.TText{+line, +col, s}:
      col
    case L.TOpen{+line, +col}:
      col
    case L.TOther{+line, +col, +b}:
      col
    case L.TPun{+line, +col, +b}:
      col
    case L.TOp{+line, +col, s}:
      col

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
      groups.go(rest, groups.step(U32.is_eq(tok_col(t), 0), t, a))
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
          missing_language(tok_line(t))

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
# mutual recursion for a parser that descends: a stack of open frames
# (a list's `[`, a `(`, an infix operator waiting for its right operand)
# and the mode, an operand wanted or one in hand. Precedence in glam is a
# partial relation (docs/Syntax.md, Operators): a chain of one operator
# needs no parentheses, two different ones do. `++` is the one known so
# far; its chains group to the right, append being associative.

type Fr is Data:
  # an open `[`: its line, the members so far reversed, and how it
  # stands: 0 just opened, 1 after a leading comma, 2 after a member's
  # comma
  FList{+line: U32, xs: List<&2, Expr>, +sep: U32}
  FParen{+line: U32}
  FOp{+line: U32, op: List<&2, U32>, a: Expr}

type Pm is Data:
  MWant{st: List<&2, Fr>}
  MHave{st: List<&2, Fr>, e: Expr}
  # after a name and `.`: the path so far
  MDot{st: List<&2, Fr>, +line: U32, path: List<&2, List<&2, U32>>}
  MFail{d: Diag}

type Ex is Data:
  XOk{e: Expr}
  XErr{d: Diag}

def fail(+line: U32, msg: String) -> Pm:
  MFail{Diag{line, msg}}

def no_right(+line: U32) -> Pm:
  fail(line, "an infix operator requires a right operand")

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

def word.k(+kind: U32, st: List<&2, Fr>, +line: U32, +s: List<&2, U32>) -> Pm:
  match kind:
    case 1:
      number(st, line, s)
    case 2:
      MHave{st, EName{line, [s]}}
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
    case L.TOp{+l, +c, s}:
      fail(l, "expected an expression before " ++ str(s))
    case L.TEq{+l, +c}:
      fail(l, "expected an expression, found =")
    case L.TDot{+l, +c}:
      fail(l, "expected an expression, found .")
    case L.TOther{+l, +c, +b}:
      fail(l, "unexpected character " ++ str([b]))

# Operators, commas and closers after an operand
# ----------------------------------------------

type Rd is Data:
  Rd{st: List<&2, Fr>, e: Expr}

# the operators waiting on top of the stack applied, the latest first,
# so that a chain of one operator groups to the right
def reduce(st: List<&2, Fr>, e: Expr) -> Rd:
  match st:
    case Nil{}:
      Rd{Nil{}, e}
    case Con{f, rest}:
      match f:
        case FOp{+line, op, a}:
          reduce(rest, EOp2{line, op, a, e})
        case FList{+line, xs, +sep}:
          Rd{Con{FList{line, xs, sep}, rest}, e}
        case FParen{+line}:
          Rd{Con{FParen{line}, rest}, e}

def have.op.k(+known: Bool, st: List<&2, Fr>, e: Expr, +line: U32, op: List<&2, U32>) -> Pm:
  match known:
    case True{}:
      MWant{Con{FOp{line, op, e}, st}}
    case False{}:
      fail(line, "the operator " ++ str(op) ++ " is not supported yet")

def have.op(st: List<&2, Fr>, e: Expr, +line: U32, +op: List<&2, U32>) -> Pm:
  have.op.k(bytes_eq(op, [43, 43]), st, e, line, op)

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
            case FOp{+l, op, a}:
              fail(line, "an operator left waiting")

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
            case FOp{+l, op, a}:
              fail(line, "an operator left waiting")

def have.pun(st: List<&2, Fr>, e: Expr, +line: U32, +b: U32) -> Pm:
  match b:
    case 44:
      have.comma(reduce(st, e), line)
    case 93:
      have.close(reduce(st, e), line, 93)
    case 41:
      have.close(reduce(st, e), line, 41)
    case _:
      fail(line, "this form is not supported yet: " ++ str([b]))

# `.` after an operand: a path goes on after a name
def have.dot(e: Expr, st: List<&2, Fr>, +line: U32) -> Pm:
  match e:
    case EName{+l, path}:
      MDot{st, l, path}
    case _:
      fail(line, "a field of an expression is not supported yet")

# an operand in hand
def have(st: List<&2, Fr>, e: Expr, t: L.Tok) -> Pm:
  match t:
    case L.TOp{+l, +c, s}:
      have.op(st, e, l, s)
    case L.TPun{+l, +c, +b}:
      have.pun(st, e, l, b)
    case L.TDot{+l, +c}:
      have.dot(e, st, l)
    case L.TWord{+l, +c, s}:
      fail(l, "function application is not supported yet: " ++ str(s))
    case L.TText{+l, +c, s}:
      fail(l, "function application is not supported yet: a text")
    case L.TOpen{+l, +c}:
      fail(l, "a text is not closed on its line")
    case L.TEq{+l, +c}:
      fail(l, "unexpected =")
    case L.TOther{+l, +c, +b}:
      fail(l, "unexpected character " ++ str([b]))

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

def step(m: Pm, t: L.Tok) -> Pm:
  match m:
    case MFail{d}:
      MFail{d}
    case MWant{st}:
      want(st, t)
    case MHave{st, e}:
      have(st, e, t)
    case MDot{st, +line, path}:
      dot(st, line, path, t)

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

def body.x(x: Ex, +line: U32, path: List<&2, List<&2, U32>>) -> Dc:
  match x:
    case XOk{e}:
      DOk{Def{line, path, e}}
    case XErr{d}:
      DErr{d}

# the body after `=`: an expression, to the declaration's end
def body(ts: List<&2, L.Tok>, +line: U32, path: List<&2, List<&2, U32>>) -> Dc:
  body.x(end(expr.go(ts, MWant{Nil{}}), line), line, path)

# a path being read: the names so far reversed and whether a name is
# expected next (after `.`, or at the start) or `.` or `=`; then the body
# begins, or the declaration failed
type Ps is Data:
  PNext{acc: List<&2, List<&2, U32>>, +name: Bool}
  PBody{path: List<&2, List<&2, U32>>}
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

# one token of a path, by its kind, a name expected or not
def path.step.k(+kind: U32, +s: List<&2, U32>, shown: String, +line: U32, acc: List<&2, List<&2, U32>>, +name: Bool) -> Ps:
  match kind name:
    case 1 True{}:
      path.word(name_ok(s), line, s, acc)
    case 2 False{}:
      PNext{acc, True{}}
    case 3 False{}:
      PBody{List.reverse(&2, List<&2, U32>, acc)}
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
        case PBody{path}:
          body(Con{t, rest}, line, path)
        case PFail{d}:
          DErr{d}
    case Nil{}:
      match st:
        case PNext{acc, +name}:
          path.end(name, line)
        case PBody{path}:
          body(Nil{}, line, path)
        case PFail{d}:
          DErr{d}

def decl(g: List<&2, L.Tok>) -> Dc:
  match g:
    case Nil{}:
      DErr{Diag{0, "an empty declaration"}}
    case Con{+t, rest}:
      path.go(Con{t, rest}, PNext{Nil{}, True{}}, tok_line(t))

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
          PErr{[Diag{tok_line(t), "expected a declaration at column 0, found " ++ tok_show(t)}]}
        case Nil{}:
          parse.gs(Nil{}, na)

# the first token must stand at column 0
def parse.first(ts: List<&2, L.Tok>, +na: U32) -> Parsed:
  match ts:
    case Con{+t, rest}:
      parse.first.k(U32.is_eq(tok_col(t), 0), Con{t, rest}, na)
    case Nil{}:
      parse.gs(Nil{}, na)

def parse(lx: L.Lx) -> Parsed:
  match lx:
    case L.Lx{toks, +na}:
      parse.first(toks, na)
