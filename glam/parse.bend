import Base
import ./lex.bend as L

# The ".g" parser, as far as the hello ladder has climbed (HelloLadder,
# ladder-text): the language declaration first (docs/Syntax.md, Language
# Version Declaration), then definitions `path = Expr`, each declaration
# beginning at column 0 and continuing on indented lines (Toplevel
# Structure). Expressions are texts alone for now. Diagnostics carry the
# line of the declaration they are about, as samples/invalid's .expect
# files name them; every declaration is read, so that one file reports
# all its errors.
#
# Bend admits no mutual recursion and no match on a computed value, so
# each loop here is one function recurring on its list, the step it takes
# computed by a helper into a value the next call matches as a parameter.

type Expr is Data:
  EText{s: List<&2, U32>}

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

# after a text: nothing more, for now
def body.end(ts: List<&2, L.Tok>, +line: U32, path: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Dc:
  match ts:
    case Nil{}:
      DOk{Def{line, path, EText{s}}}
    case Con{t, rest}:
      DErr{Diag{line, "this form is not supported yet: " ++ tok_show(t)}}

# the body after `=`: a text, for now
def body(ts: List<&2, L.Tok>, +line: U32, path: List<&2, List<&2, U32>>) -> Dc:
  match ts:
    case Nil{}:
      DErr{Diag{line, "expected an expression after ="}}
    case Con{+t, rest}:
      match t:
        case L.TText{+l, +c, s}:
          body.end(rest, line, path, s)
        case L.TOpen{+l, +c}:
          DErr{Diag{line, "a text is not closed on its line"}}
        case _:
          DErr{Diag{line, "this form is not supported yet: " ++ tok_show(t)}}

# a path being read: the names so far reversed and whether a name is
# expected next (after `.`, or at the start) or `.` or `=`; then the body
# begins, or the declaration failed
type Ps is Data:
  PNext{acc: List<&2, List<&2, U32>>, +name: Bool}
  PBody{path: List<&2, List<&2, U32>>}
  PFail{d: Diag}

def name_ok(s: List<&2, U32>) -> Bool:
  match s:
    case Con{+b, rest}:
      L.is_letter(b)
    case Nil{}:
      False{}

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
