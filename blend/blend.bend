import Base

# Blend: static objects for Bend (blend/README.md; the plan,
# docs/plans/Blend_2026-11-04.md). It reads a `.blend` file into its
# structure (`blend-read`), checks its objects (`blend-objects`), binds
# the names in each concrete object's copies (`blend-resolve`) and emits
# the module (`blend-emit`); each command runs the stages up to its own
# (The command line, at the end). Run it built (blend/run.sh).
#
# Bend has no mutual recursion, so the source is read in two passes: the
# lines into a flat list of items, each with its line and indentation (an
# import, an object's header, a declaration, a definition's header with
# its body's lines), then the items into a tree, objects nesting by
# indentation, a stack of the objects being read; each body's lines become
# Bend's tokens as its definition joins the tree. A line Blend cannot read
# is kept as such (`?` when printed), for a later step to report: reading
# never fails. Bend matches only variables and has no mutual recursion, so
# a decision on a computed value goes through `when`, its arms thunks, a
# loop's next turn inside an arm; a loop that does not shrink its input
# structurally runs on fuel.

# Decisions
# =========

# a decision on a computed value: Bend matches only variables, so the arms
# are thunks, and a loop's next turn sits in an arm, inside the loop

def when(-R: Type, c: Bool, yes: Unit -> R, no: Unit -> R) -> R:
  match c:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def on.maybe(-A: Data, -R: Type, m: Maybe<&2, A>, none: Unit -> R, some: A -> R) -> R:
  match m:
    case None{}:
      none(Unit{})
    case Some{+x}:
      some(x)

def on.pair(-A: Type, -B: Type, -R: Type, p: A & B, f: A -> B -> R) -> R:
  (a, b) = p
  f(a, b)

# Text
# ====
#
# Source text is a list of byte codes, made a String only for output.

def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), codes(t)}

def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{+h, t}:
      SCon{Char.from_u32(h), text(t)}

# whether xs begins with p
def starts(xs: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match xs p:
    case _ Nil{}:
      True{}
    case Nil{} Con{ph, pt}:
      False{}
    case Con{+xh, xt} Con{+ph, pt}:
      U32.is_eq(xh, ph) && starts(xt, pt)

def same(xs: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match xs p:
    case Nil{} Nil{}:
      True{}
    case Con{+xh, xt} Con{+ph, pt}:
      U32.is_eq(xh, ph) && same(xt, pt)
    case _ _:
      False{}

def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+k:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop(k, t)

# xs without its leading spaces, and how many there were
def ltrim.go(xs: List<&2, U32>, +n: U32) -> U32 & List<&2, U32>:
  match xs:
    case Nil{}:
      (n, Nil{})
    case Con{+h, t}:
      match h:
        case 32:
          ltrim.go(t, (n + 1 : U32))
        case _:
          (n, Con{h, t})

def ltrim.fin(r: U32 & List<&2, U32>) -> List<&2, U32>:
  (+n, xs) = r
  xs

def ltrim(xs: List<&2, U32>) -> List<&2, U32>:
  ltrim.fin(ltrim.go(xs, 0))

# xs without its trailing spaces
def rtrim(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, ltrim(List.reverse(&2, U32, xs)))

def trim(xs: List<&2, U32>) -> List<&2, U32>:
  rtrim(ltrim(xs))

def until.go(xs: List<&2, U32>, +c: U32, +acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match xs:
    case Nil{}:
      (List.reverse(&2, U32, acc), Nil{})
    case Con{+h, +t}:
      when(List<&2, U32> & List<&2, U32>, U32.is_eq(h, c), u => (List.reverse(&2, U32, acc), t), u => until.go(t, c, Con{h, acc}))

# xs up to the first c, and what follows it (c dropped)
def until(xs: List<&2, U32>, +c: U32) -> List<&2, U32> & List<&2, U32>:
  until.go(xs, c, Nil{})

# xs split at its commas outside any bracket, each part trimmed
def commas.add(x: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match x:
    case Nil{}:
      out
    case Con{h, t}:
      Con{Con{h, t}, out}

def commas.end(cur: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  commas.add(trim(List.reverse(&2, U32, cur)), out)

# a closer at depth 0 leaves it there: the text is Bend's to judge
def depth.dec(+d: U32) -> U32:
  match d:
    case 0:
      0
    case _:
      (d - 1 : U32)

# a `>` after `-` is an arrow, not a bracket
def depth.gt(+prev: U32, +d: U32) -> U32:
  match prev:
    case 45:
      d
    case _:
      depth.dec(d)

# the bracket depth after h, prev the byte before it
def depth.next(+prev: U32, +h: U32, +d: U32) -> U32:
  match h:
    case 40:
      (d + 1 : U32)
    case 60:
      (d + 1 : U32)
    case 123:
      (d + 1 : U32)
    case 91:
      (d + 1 : U32)
    case 41:
      depth.dec(d)
    case 62:
      depth.gt(prev, d)
    case 125:
      depth.dec(d)
    case 93:
      depth.dec(d)
    case _:
      d

def commas.go(xs: List<&2, U32>, +prev: U32, +depth: U32, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, commas.end(cur, out))
    case Con{+h, +t}:
      when(List<&2, List<&2, U32>>, U32.is_eq(h, 44) && U32.is_eq(depth, 0),
        u => commas.go(t, h, depth, Nil{}, commas.end(cur, out)),
        u => commas.go(t, h, depth.next(prev, h, depth), Con{h, cur}, out))

def commas(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  commas.go(xs, 0, 0, Nil{}, Nil{})

# Lines
# =====

# a line of the source: its number, its indentation, its text after it;
# a carriage return dropped wherever it is
type Ln is Data:
  Ln{+no: U32, +ind: U32, txt: List<&2, U32>}

# a line read: its indentation's spaces counted in n, a Nat, exact
# however many, then its text
def line.of(xs: List<&2, U32>, +n: Nat, +no: U32) -> Ln:
  match xs:
    case Nil{}:
      Ln{no, U32.from_nat(n), Nil{}}
    case Con{+h, +t}:
      when(Ln, U32.is_eq(h, 32), u => line.of(t, 1n+n, no), u => Ln{no, U32.from_nat(n), Con{h, t}})

def lines.line(cur: List<&2, U32>, +no: U32) -> Ln:
  line.of(List.reverse(&2, U32, cur), 0n, no)

# the lines, a newline ending each, a carriage return dropped; the bytes
# tested, not matched, so that a law can follow (blend/LAWS.bend,
# `lines.join`)
def lines.go(bs: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, Ln>) -> List<&2, Ln>:
  match bs:
    case Nil{}:
      List.reverse(&2, Ln, Con{lines.line(cur, no), out})
    case Con{+b, +t}:
      when(List<&2, Ln>, U32.is_eq(b, 10), u => lines.go(t, Nil{}, (no + 1 : U32), Con{lines.line(cur, no), out}),
        u => when(List<&2, Ln>, U32.is_eq(b, 13), v => lines.go(t, cur, no, out), v => lines.go(t, Con{b, cur}, no, out)))

# a file's lines numbered from base + 1 (Locations, below)
def lines.at(bs: List<&2, U32>, +base: U32) -> List<&2, Ln>:
  lines.go(bs, Nil{}, (base + 1 : U32), Nil{})

def lines(bs: List<&2, U32>) -> List<&2, Ln>:
  lines.at(bs, 0)

# a line as written: its indentation's spaces, then its text
# (blend/LAWS.bend, `lines.join`)
def ln.text(l: Ln) -> List<&2, U32>:
  match l:
    case Ln{+no, +ind, txt}:
      List.append(&2, U32, List.replicate(U32, U32.to_nat(ind), 32), txt)

# lines joined back, a newline between each two
def lines.text(ls: List<&2, Ln>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match t:
        case Nil{}:
          ln.text(l)
        case Con{h, r}:
          List.append(&2, U32, ln.text(l), Con{10, lines.text(Con{h, r})})

# bytes, their carriage returns dropped
def uncr(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, +t}:
      when(List<&2, U32>, U32.is_eq(b, 13), u => uncr(t), u => Con{b, uncr(t)})

def blank(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def comment(xs: List<&2, U32>) -> Bool:
  starts(xs, codes("#"))

# Tokens
# ======
#
# A body's lines as Bend's tokens, so that its references can be found and
# rewritten while the rest passes through as written: a name, the dots
# within it and its mark (`_` begins a name; `^`, `^^` and `~` are kept
# with the name they mark); a number with its suffix (`0n`); a string or a
# char; a comment, the rest of its line; a run of spaces; any other byte
# alone.

type Tok is Data:
  TName{txt: List<&2, U32>}
  TNum{txt: List<&2, U32>}
  TStr{txt: List<&2, U32>}
  TCom{txt: List<&2, U32>}
  TSp{txt: List<&2, U32>}
  TSym{+c: U32}

# a body's line: its number, its indentation, its tokens
type Bl is Data:
  Bl{+no: U32, +ind: U32, toks: List<&2, Tok>}

# a byte's class, as the tokens go by it: a space or a tab, a letter or
# `_`, a digit, `.`, `"`, `#`, `^`, `~`, a backslash, `'`, any other. A
# datatype, so that a law can follow the tokenizer's choices
# (blend/LAWS.bend, `tokens.spell`): a byte's match leaves a proof stuck
type Cl is Data:
  CSp{}
  CAlpha{}
  CDigit{}
  CDot{}
  CQuote{}
  CHash{}
  CCaret{}
  CTilde{}
  CBack{}
  CTick{}
  COther{}

def cls.of(+alpha: Bool, +digit: Bool, +h: U32) -> Cl:
  match alpha digit:
    case True{} _:
      CAlpha{}
    case False{} True{}:
      CDigit{}
    case False{} False{}:
      match h:
        case 32:
          CSp{}
        case 9:
          CSp{}
        case 95:
          CAlpha{}
        case 46:
          CDot{}
        case 34:
          CQuote{}
        case 35:
          CHash{}
        case 94:
          CCaret{}
        case 126:
          CTilde{}
        case 92:
          CBack{}
        case 39:
          CTick{}
        case _:
          COther{}

def cls(+h: U32) -> Cl:
  cls.of((U32.is_ge(h, 65) && U32.is_le(h, 90)) || (U32.is_ge(h, 97) && U32.is_le(h, 122)),
    U32.is_ge(h, 48) && U32.is_le(h, 57), h)

def classes(xs: List<&2, U32>) -> List<&2, Cl>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{cls(h), classes(t)}

# the classes' tests: a name's first byte (a letter or `_`), a name's
# rest (letters, digits, `_` and `.`), a number's rest (letters and
# digits, its suffix among them), a space, a caret, a backslash, `"`, `'`
def cl.alpha(c: Cl) -> Bool:
  match c:
    case CAlpha{}:
      True{}
    case _:
      False{}

def cl.name(c: Cl) -> Bool:
  match c:
    case CAlpha{}:
      True{}
    case CDigit{}:
      True{}
    case CDot{}:
      True{}
    case _:
      False{}

def cl.alnum(c: Cl) -> Bool:
  match c:
    case CAlpha{}:
      True{}
    case CDigit{}:
      True{}
    case _:
      False{}

def cl.sp(c: Cl) -> Bool:
  match c:
    case CSp{}:
      True{}
    case _:
      False{}

def cl.caret(c: Cl) -> Bool:
  match c:
    case CCaret{}:
      True{}
    case _:
      False{}

def cl.back(c: Cl) -> Bool:
  match c:
    case CBack{}:
      True{}
    case _:
      False{}

def cl.quote(c: Cl) -> Bool:
  match c:
    case CQuote{}:
      True{}
    case _:
      False{}

def cl.tick(c: Cl) -> Bool:
  match c:
    case CTick{}:
      True{}
    case _:
      False{}

def name.rest(cs: List<&2, Cl>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      cl.name(c) && name.rest(t)

def name.first(cs: List<&2, Cl>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      cl.alpha(c) && name.rest(t)

# a name as Bend's: a letter or `_`, then letters, digits, `_` and `.`
def name.ok(xs: List<&2, U32>) -> Bool:
  name.first(classes(xs))

def names.ok(ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, t}:
      name.ok(n) && names.ok(t)

# a run read: its bytes, reversed, and the bytes after it with their classes
type Rn is Data:
  Rn{acc: List<&2, U32>, xs: List<&2, U32>, cs: List<&2, Cl>}

def rn.acc(r: Rn) -> List<&2, U32>:
  match r:
    case Rn{acc, xs, cs}:
      acc

def rn.xs(r: Rn) -> List<&2, U32>:
  match r:
    case Rn{acc, xs, cs}:
      xs

def rn.cs(r: Rn) -> List<&2, Cl>:
  match r:
    case Rn{acc, xs, cs}:
      cs

# a run of the bytes whose classes p takes: a name's rest, a number's, the
# spaces, the carets
def run.while(~p: Cl -> Bool, xs: List<&2, U32>, cs: List<&2, Cl>, +acc: List<&2, U32>) -> Rn:
  match xs cs:
    case Con{+h, +t} Con{+c, +ct}:
      when(Rn, p(c), u => run.while(~p, t, ct, Con{h, acc}), u => Rn{acc, Con{h, t}, Con{c, ct}})
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a quoted run's rest, to its closing quote, whose class shut takes (a
# string's `"`, a char's `'`), a backslash escaping the byte after it;
# esc, a backslash read before
def run.quoted(~shut: Cl -> Bool, xs: List<&2, U32>, cs: List<&2, Cl>, +acc: List<&2, U32>, +esc: Bool) -> Rn:
  match xs cs:
    case Con{+h, +t} Con{+c, +ct}:
      when(Rn, shut(c) && Bool.not(esc), u => Rn{Con{h, acc}, t, ct},
        u => run.quoted(~shut, t, ct, Con{h, acc}, cl.back(c) && Bool.not(esc)))
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# the name after a run of `^`
def run.host(+r: Rn) -> Rn:
  run.while(~cl.name, rn.xs(r), rn.cs(r), rn.acc(r))

# a line's tokens, one a turn; fuel, the line's length, as each turn
# takes a byte at least
def toks.go(n: Nat, xs: List<&2, U32>, cs: List<&2, Cl>, +out: List<&2, Tok>) -> List<&2, Tok>:
  match n:
    case 0n:
      List.reverse(&2, Tok, out)
    case 1n++k:
      match xs cs:
        case Con{+h, +t} Con{c, +ct}:
          match c:
            case CSp{}:
              +r = run.while(~cl.sp, t, ct, [h])
              toks.go(k, rn.xs(r), rn.cs(r), Con{TSp{List.reverse(&2, U32, rn.acc(r))}, out})
            case CAlpha{}:
              +r = run.while(~cl.name, t, ct, [h])
              toks.go(k, rn.xs(r), rn.cs(r), Con{TName{List.reverse(&2, U32, rn.acc(r))}, out})
            case CDigit{}:
              +r = run.while(~cl.alnum, t, ct, [h])
              toks.go(k, rn.xs(r), rn.cs(r), Con{TNum{List.reverse(&2, U32, rn.acc(r))}, out})
            case CQuote{}:
              +r = run.quoted(~cl.quote, t, ct, [h], False{})
              toks.go(k, rn.xs(r), rn.cs(r), Con{TStr{List.reverse(&2, U32, rn.acc(r))}, out})
            case CHash{}:
              List.reverse(&2, Tok, Con{TCom{Con{h, t}}, out})
            case CCaret{}:
              +r = run.host(run.while(~cl.caret, t, ct, [h]))
              toks.go(k, rn.xs(r), rn.cs(r), Con{TName{List.reverse(&2, U32, rn.acc(r))}, out})
            case CTilde{}:
              +r = run.while(~cl.name, t, ct, [h])
              toks.go(k, rn.xs(r), rn.cs(r), Con{TName{List.reverse(&2, U32, rn.acc(r))}, out})
            case CTick{}:
              +r = run.quoted(~cl.tick, t, ct, [h], False{})
              toks.go(k, rn.xs(r), rn.cs(r), Con{TStr{List.reverse(&2, U32, rn.acc(r))}, out})
            case CDot{}:
              toks.go(k, t, ct, Con{TSym{h}, out})
            case CBack{}:
              toks.go(k, t, ct, Con{TSym{h}, out})
            case COther{}:
              toks.go(k, t, ct, Con{TSym{h}, out})
        case _ _:
          List.reverse(&2, Tok, out)

def toks(+xs: List<&2, U32>) -> List<&2, Tok>:
  toks.go(List.length(&2, U32, xs), xs, classes(xs), Nil{})

def tok.bytes(t: Tok) -> List<&2, U32>:
  match t:
    case TName{x}:
      x
    case TNum{x}:
      x
    case TStr{x}:
      x
    case TCom{x}:
      x
    case TSp{x}:
      x
    case TSym{+c}:
      [c]

# the bytes tokens spell, each token's in turn (blend/LAWS.bend,
# `tokens.spell`)
def toks.text(ts: List<&2, Tok>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      List.append(&2, U32, tok.bytes(t), toks.text(r))

def toks.lines(ls: List<&2, Ln>) -> List<&2, Bl>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, +txt}:
          Con{Bl{no, ind, toks(txt)}, toks.lines(t)}

# Items
# =====

# sharing: 0 affine, the default; 1 shared; 2 copied
type Item is Data:
  IImport{txt: List<&2, U32>, +no: U32, +ind: U32}
  IObj{+abs: Bool, +with: Bool, +ext: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, +no: U32, +ind: U32}
  IDecl{names: List<&2, List<&2, U32>>, +no: U32, +ind: U32}
  IDef{+share: U32, +upd: Bool, name: List<&2, U32>, rest: List<&2, U32>, params: List<&2, List<&2, U32>>, body: List<&2, Ln>, +no: U32, +ind: U32, +what: U32}
  IBad{txt: List<&2, U32>, +no: U32, +ind: U32}
  IBend{lines: List<&2, Ln>, +no: U32, +ind: U32}

# a parameter's name: its marks (+ - ~ @) dropped, up to its colon; a
# template's (~) or an erased one's (-) mark kept, for a witness to pass
# it on as Bend takes it
def param.first(r: List<&2, U32> & List<&2, U32>) -> List<&2, U32>:
  (nm, rest) = r
  trim(nm)

def param.plain(p: List<&2, U32>) -> List<&2, U32>:
  param.first(until(p, 58))

def param.m(+h: U32, t: List<&2, U32>) -> List<&2, U32>:
  match h:
    case 43:
      param.plain(t)
    case 64:
      param.plain(t)
    case 126:
      Con{126, param.plain(t)}
    case 45:
      Con{45, param.plain(t)}
    case _:
      param.plain(Con{h, t})

def param.name(p: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      param.m(h, t)

def params.go(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{param.name(p), params.go(t)}

# the parameter list between a header's first parenthesis and its match
def parens.go(xs: List<&2, U32>, +prev: U32, +depth: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{+h, +t}:
      when(List<&2, U32>, U32.is_eq(h, 41) && U32.is_eq(depth, 0), u => List.reverse(&2, U32, acc),
        u => parens.go(t, h, depth.next(prev, h, depth), Con{h, acc}))

def parens(xs: List<&2, U32>) -> List<&2, U32>:
  parens.go(xs, 0, 0, Nil{})

def def.named(+ok: Bool, name: List<&2, U32>, +rest: List<&2, U32>, xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IDef{share, upd, name, Con{40, rest}, params.go(commas(parens(rest))), body, no, ind, 0}
    case False{}:
      IBad{xs, no, ind}

# a name, then its parameters: the parenthesis found
def def.r(r: List<&2, U32> & List<&2, U32>, xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  (+name, +rest) = r
  def.named(name.ok(trim(name)) && Bool.not(blank(rest)), trim(name), rest, xs, share, upd, body, no, ind)

# after `def ` or `upd `: the name up to its parenthesis, the rest kept
def def.item(+xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.r(until(xs, 40), xs, share, upd, body, no, ind)

# after `upd `, a definition's update: `upd def f(...)`, or `upd f(...)`,
# sugar for it (the maintainer, 2026-11-04), as `upd type` is a type's
def upd.def(+xs: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(xs, codes("def ")), u => drop(4n, xs), u => xs)

def def.kw.d(+d: Bool, +u: Bool, xs: List<&2, U32>, +share: U32, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match d u:
    case True{} _:
      def.item(drop(4n, xs), share, False{}, body, no, ind)
    case False{} True{}:
      def.item(upd.def(drop(4n, xs)), share, True{}, body, no, ind)
    case False{} False{}:
      IBad{xs, no, ind}

def def.kw(+xs: List<&2, U32>, +share: U32, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.kw.d(starts(xs, codes("def ")), starts(xs, codes("upd ")), xs, share, body, no, ind)

def def.share.s(+s: Bool, +c: Bool, xs: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match s c:
    case True{} _:
      def.kw(drop(7n, xs), 1, body, no, ind)
    case False{} True{}:
      def.kw(drop(7n, xs), 2, body, no, ind)
    case False{} False{}:
      def.kw(xs, 0, body, no, ind)

# a definition's header, its sharing first if stated
def def.share(+xs: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.share.s(starts(xs, codes("shared ")), starts(xs, codes("copied ")), xs, body, no, ind)

def is_def(+xs: List<&2, U32>) -> Bool:
  starts(xs, codes("def ")) || starts(xs, codes("upd ")) || starts(xs, codes("shared ")) || starts(xs, codes("copied ")) ||
    starts(xs, codes("law ")) || starts(xs, codes("proof "))

def obj.with.s(+w: Bool, rx: List<&2, U32>) -> List<&2, U32>:
  match w:
    case True{}:
      drop(5n, rx)
    case False{}:
      rx

def obj.with.r(+rx: List<&2, U32>) -> List<&2, U32>:
  obj.with.s(starts(rx, codes("htiw ")), rx)

# the parents' text, ` with` at its end dropped
def obj.with(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, obj.with.r(List.reverse(&2, U32, xs)))

def obj.parents.e(+e: Bool, rest: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match e:
    case True{}:
      commas(obj.with(drop(8n, rest)))
    case False{}:
      Nil{}

def obj.parents(+rest: List<&2, U32>) -> List<&2, List<&2, U32>>:
  obj.parents.e(starts(rest, codes("extends ")), rest)

def obj.named(+ok: Bool, +with: Bool, +ext: Bool, name: List<&2, U32>, ps: List<&2, List<&2, U32>>, xs: List<&2, U32>, +abs: Bool, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IObj{abs, with, ext, name, ps, no, ind}
    case False{}:
      IBad{xs, no, ind}

# after the name: `extends A, B`, each parent a name, or nothing, then
# `with` before members; an object with none may leave it out
def obj.rest(+rest: List<&2, U32>, +name: List<&2, U32>, xs: List<&2, U32>, +abs: Bool, +ext: Bool, +no: U32, +ind: U32) -> Item:
  obj.named(name.ok(name) && (blank(rest) || same(rest, codes("with")) ||
      (starts(rest, codes("extends ")) && names.ok(obj.parents(rest)))),
    same(rest, codes("with")) || starts(List.reverse(&2, U32, rest), codes("htiw ")), ext,
    name, obj.parents(rest), xs, abs, no, ind)

def obj.ext(r: List<&2, U32> & List<&2, U32>, xs: List<&2, U32>, +abs: Bool, +ext: Bool, +no: U32, +ind: U32) -> Item:
  (name, rest) = r
  obj.rest(rtrim(rest), name, xs, abs, ext, no, ind)

# `object Name [extends A, B] [with]`, `abstract` before it or not
def obj.item(xs: List<&2, U32>, line: List<&2, U32>, +abs: Bool, +ext: Bool, +no: U32, +ind: U32) -> Item:
  obj.ext(until(xs, 32), line, abs, ext, no, ind)

def decl.named(+ok: Bool, ns: List<&2, List<&2, U32>>, line: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IDecl{ns, no, ind}
    case False{}:
      IBad{line, no, ind}

def decl.some(ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{n, t}:
      True{}

# `declare a, b`, each a name
def decl.item(+ns: List<&2, List<&2, U32>>, line: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  decl.named(decl.some(ns) && names.ok(ns), ns, line, no, ind)

# a line's body lines: those after it, blank or indented deeper than ind,
# and the lines after them
def body.go(ls: List<&2, Ln>, +ind: U32, +acc: List<&2, Ln>) -> List<&2, Ln> & List<&2, Ln>:
  match ls:
    case Nil{}:
      (List.reverse(&2, Ln, acc), Nil{})
    case Con{l, +t}:
      match l:
        case Ln{+no, +li, +txt}:
          when(List<&2, Ln> & List<&2, Ln>, blank(txt) || U32.is_gt(li, ind), u => body.go(t, ind, Con{Ln{no, li, txt}, acc}),
            u => (List.reverse(&2, Ln, acc), Con{Ln{no, li, txt}, t}))

# lines, their leading blank ones dropped
def body.lead(ls: List<&2, Ln>) -> List<&2, Ln>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, +t}:
      match l:
        case Ln{+no, +ind, +txt}:
          when(List<&2, Ln>, blank(txt), u => body.lead(t), u => Con{Ln{no, ind, txt}, t})

# a body, its trailing blank lines dropped
def body.trim(ls: List<&2, Ln>) -> List<&2, Ln>:
  List.reverse(&2, Ln, body.lead(List.reverse(&2, Ln, ls)))

# The flat pass
# -------------

# Typed declarations
#
# `declare def f(params) -> T`, or its sugar `declare f(params) -> T`, and
# `declare type S: K` or `declare type P(params): K`, each a declaration
# of its name and a witness of what the name must be: a member of its
# own (what 4), named the name and `!` inside Blend, `f.as_declared`
# outside, written in the proofs' file for each concrete object, bound to
# its finals, where Bend checks that the object's f fits
# (`blend-declares-witnessed`). `declare a, b` and `declare type S` are
# untyped, as before.

def decl.witness(+name: List<&2, U32>, +ps: List<&2, U32>, +ret: List<&2, U32>, +txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  when(List<&2, Item>, name.ok(name) && Bool.not(blank(ret)),
    u => Con{IDef{0, False{}, List.append(&2, U32, name, [33]), List.append(&2, U32, Con{40, ps}, List.append(&2, U32, codes(") -> "), List.append(&2, U32, ret, codes(":")))),
      params.go(commas(ps)), Nil{}, no, ind, 4}, Con{IDecl{[name], no, ind}, out}},
    u => Con{IBad{txt, no, ind}, out})

# whether xs holds p
def holds(+xs: List<&2, U32>, +p: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      blank(p)
    case Con{+h, +t}:
      starts(Con{h, t}, p) || holds(t, p)

# `f(params) -> T`
def decl.def.k(r: List<&2, U32> & List<&2, U32>, +txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  (+name, +rest) = r
  when(List<&2, Item>, holds(rest, codes(") ->")),
    u => decl.witness(trim(name), parens(rest), trim(drop(Nat.add(List.length(&2, U32, parens(rest)), 4n), rest)), txt, no, ind, out),
    u => Con{IBad{txt, no, ind}, out})

# after the parameters, `: KIND` or nothing, for `Type`
def type.kind(+r: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(r, codes(":")), u => trim(drop(1n, r)), u => codes("Type"))

# `S: K`, or `P(params): K`
def decl.type.k(r: List<&2, U32> & List<&2, U32>, +txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  (+name, +after) = r
  when(List<&2, Item>, starts(after, codes("(")),
    u => decl.witness(name, parens(List.tail(&2, U32, after)),
      type.kind(trim(drop(Nat.add(List.length(&2, U32, parens(List.tail(&2, U32, after))), 2n), after))), txt, no, ind, out),
    u => decl.witness(name, Nil{}, type.kind(trim(after)), txt, no, ind, out))

# a name's letters, and what follows them
def name.split(xs: List<&2, U32>, cs: List<&2, Cl>, +acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match xs cs:
    case Con{+h, +t} Con{c, +ct}:
      when(List<&2, U32> & List<&2, U32>, cl.name(c),
        u => name.split(t, ct, Con{h, acc}), u => (List.reverse(&2, U32, acc), Con{h, t}))
    case _ _:
      (List.reverse(&2, U32, acc), Nil{})

def decl.type.line(+r: List<&2, U32>, +txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  when(List<&2, Item>, holds(r, codes(":")) || holds(r, codes("(")), u => decl.type.k(name.split(r, classes(r), Nil{}), txt, no, ind, out),
    u => Con{decl.item(commas(r), txt, no, ind), out})

# what follows `declare `
def decl.line(+rest: List<&2, U32>, +txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  when(List<&2, Item>, starts(rest, codes("type ")), u => decl.type.line(trim(drop(5n, rest)), txt, no, ind, out),
    u => when(List<&2, Item>, holds(rest, codes("(")),
      v => decl.def.k(until(when(List<&2, U32>, starts(rest, codes("def ")), w => drop(4n, rest), w => rest), 40), txt, no, ind, out),
      v => Con{decl.item(commas(rest), txt, no, ind), out}))

# a line that is no definition's header: an item, or nothing for a blank
# line or a comment
def flat.line(+skip: Bool, +imp: Bool, +abs: Bool, +obj: Bool, +decl: Bool, +txt: List<&2, U32>, +no: U32, +ind: U32, out: List<&2, Item>) -> List<&2, Item>:
  match skip imp abs obj decl:
    case True{} _ _ _ _:
      out
    case False{} True{} _ _ _:
      Con{IImport{txt, no, ind}, out}
    case False{} False{} True{} _ _:
      Con{obj.item(drop(16n, txt), txt, True{}, False{}, no, ind), out}
    case False{} False{} False{} True{} _:
      Con{obj.item(drop(7n, txt), txt, False{}, False{}, no, ind), out}
    case False{} False{} False{} False{} True{}:
      decl.line(drop(8n, txt), txt, no, ind, out)
    case False{} False{} False{} False{} False{}:
      Con{IBad{txt, no, ind}, out}

# Type members
#
# `type S = T`, `type S: Data = T`, `type Pair(A: Data) = A & A`, `upd`
# before: sugar for a shared definition returning the type,
# `shared def S() -> Type:` with T its body (the maintainer, 2026-11-04);
# Bend erases it. `type Name is Kind:` with its lines is a datatype of
# Bend's, passed through.

def is.member.type(+xs: List<&2, U32>) -> Bool:
  (starts(xs, codes("type ")) || starts(xs, codes("upd type "))) && holds(xs, codes(" = "))

def is.datatype(+xs: List<&2, U32>) -> Bool:
  starts(xs, codes("type ")) && Bool.not(holds(xs, codes(" = ")))

# xs split at the first p, p dropped
def split.at(xs: List<&2, U32>, +p: List<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match xs:
    case Nil{}:
      (List.reverse(&2, U32, acc), Nil{})
    case Con{+h, +t}:
      when(List<&2, U32> & List<&2, U32>, starts(Con{h, t}, p), u => (List.reverse(&2, U32, acc), drop(List.length(&2, U32, p), Con{h, t})),
        u => split.at(t, p, Con{h, acc}))

def type.made(+upd: Bool, +name: List<&2, U32>, +ps: List<&2, U32>, +after: List<&2, U32>, +ty: List<&2, U32>, xs: List<&2, U32>,
    +no: U32, +ind: U32) -> Item:
  when(Item, name.ok(name) && Bool.not(blank(ty)),
    u => IDef{1, upd, name, List.append(&2, U32, Con{40, ps}, List.append(&2, U32, codes(") -> "), List.append(&2, U32, type.kind(trim(after)), codes(":")))),
      params.go(commas(ps)), [Ln{no, (ind + 2 : U32), ty}], no, ind, 0},
    u => IBad{xs, no, ind})

# the name, then its parameters if any, then what follows them
def type.lhs(+upd: Bool, r: List<&2, U32> & List<&2, U32>, +ty: List<&2, U32>, +xs: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  (+name, +after) = r
  when(Item, starts(after, codes("(")),
    u => type.made(upd, name, parens(List.tail(&2, U32, after)), drop(Nat.add(List.length(&2, U32, parens(List.tail(&2, U32, after))), 2n), after),
      ty, xs, no, ind),
    u => type.made(upd, name, Nil{}, after, ty, xs, no, ind))

def type.eq(+upd: Bool, r: List<&2, U32> & List<&2, U32>, xs: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  (+lhs, +ty) = r
  type.lhs(upd, name.split(trim(lhs), classes(trim(lhs)), Nil{}), trim(ty), xs, no, ind)

# a type member, `type ...` or `upd type ...`
def type.item(+txt: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  when(Item, starts(txt, codes("upd ")), v => type.eq(True{}, split.at(drop(9n, txt), codes(" = "), Nil{}), txt, no, ind),
    v => type.eq(False{}, split.at(drop(5n, txt), codes(" = "), Nil{}), txt, no, ind))

# `extend N with` and `extend abstract N with`: a mixin on the nested
# object N its host has (Nested objects, below)
def ext.item(+txt: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  when(Item, starts(txt, codes("extend abstract ")), u => obj.item(drop(16n, txt), txt, True{}, True{}, no, ind),
    u => obj.item(drop(7n, txt), txt, False{}, True{}, no, ind))

def flat.item.l(+txt: List<&2, U32>, +no: U32, +ind: U32, out: List<&2, Item>) -> List<&2, Item>:
  flat.line(blank(txt) || comment(txt), starts(txt, codes("import ")), starts(txt, codes("abstract object ")),
    starts(txt, codes("object ")), starts(txt, codes("declare ")), txt, no, ind, out)

def flat.item.k(+txt: List<&2, U32>, +no: U32, +ind: U32, +out: List<&2, Item>) -> List<&2, Item>:
  when(List<&2, Item>, starts(txt, codes("extend ")), u => Con{ext.item(txt, no, ind), out}, u => flat.item.l(txt, no, ind, out))

# a header with its body: a definition, or a datatype of Bend's
# Laws and proofs
#
# `law NAME:` with its body (`for x: T` lines, then the claim), and
# `proof NAME(params):` with its proof, `upd proof` replacing one inherited
# (blend-object-laws): members, a concrete object getting its own law and
# its final proof, emitted to the module's proof file. A proof is kept by
# its law's name and a `#`, a byte no name holds, so that the two pair
# without meeting.

def law.made(+name: List<&2, U32>, +rest: List<&2, U32>, +txt: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  when(Item, name.ok(name) && blank(trim(rest)), u => IDef{0, False{}, name, codes(":"), Nil{}, body, no, ind, 1}, u => IBad{txt, no, ind})

def law.r(r: List<&2, U32> & List<&2, U32>, +txt: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  (+name, +rest) = r
  law.made(trim(name), rest, txt, body, no, ind)

# `law NAME:`, nothing after its colon
def law.item(+txt: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  law.r(until(drop(4n, txt), 58), txt, body, no, ind)

def proof.r(r: List<&2, U32> & List<&2, U32>, +upd: Bool, +txt: List<&2, U32>, +body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  (+name, +rest) = r
  when(Item, name.ok(trim(name)) && Bool.not(blank(rest)),
    u => when(Item, holds(rest, codes(") ->")),
      v => IDef{0, upd, trim(name), Con{40, rest}, params.go(commas(parens(rest))), body, no, ind, 3},
      v => IDef{0, upd, List.append(&2, U32, trim(name), [35]), Con{40, rest}, params.go(commas(parens(rest))), body, no, ind, 2}),
    u => IBad{txt, no, ind})

# `proof NAME(params):`, a law's proof, or `upd proof`; typed,
# `proof NAME(params) -> T:`, a lemma, stating what it proves
def proof.item(+txt: List<&2, U32>, +upd: Bool, +body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  when(Item, upd, u => proof.r(until(drop(10n, txt), 40), True{}, txt, body, no, ind),
    u => proof.r(until(drop(6n, txt), 40), False{}, txt, body, no, ind))

def flat.block(+txt: List<&2, U32>, +body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  when(Item, is.datatype(txt), u => IBend{Con{Ln{no, ind, txt}, body}, no, ind},
    u => when(Item, starts(txt, codes("law ")), v => law.item(txt, body, no, ind),
     v => when(Item, starts(txt, codes("upd law ")), x => IBad{txt, no, ind},
      v => when(Item, starts(txt, codes("proof ")) || starts(txt, codes("upd proof ")), w => proof.item(txt, starts(txt, codes("upd ")), body, no, ind),
        w => def.share(txt, body, no, ind)))))

# the items: a line a turn, or a definition's header with its body;
# fuel, the lines' count
def flat.go(n: Nat, ls: List<&2, Ln>, +out: List<&2, Item>) -> List<&2, Item>:
  match n:
    case 0n:
      List.reverse(&2, Item, out)
    case 1n++m:
      match ls:
        case Nil{}:
          List.reverse(&2, Item, out)
        case Con{l, +t}:
          match l:
            case Ln{+no, +ind, +txt}:
              when(List<&2, Item>, Bool.not(is.member.type(txt)) && (is_def(txt) || is.datatype(txt)),
                u => on.pair(List<&2, Ln>, List<&2, Ln>, List<&2, Item>, body.go(t, ind, Nil{}),
                  body => rest => flat.go(m, rest, Con{flat.block(txt, body.trim(body), no, ind), out})),
                u => flat.go(m, t, when(List<&2, Item>, is.member.type(txt), v => Con{type.item(txt, no, ind), out}, v => flat.item.k(txt, no, ind, out))))

def flat(+ls: List<&2, Ln>) -> List<&2, Item>:
  flat.go(List.length(&2, Ln, ls), ls, Nil{})

# The tree
# --------

type Node is Data:
  NImport{txt: List<&2, U32>, +no: U32}
  NDecl{names: List<&2, List<&2, U32>>, +no: U32}
  NDef{+share: U32, +upd: Bool, name: List<&2, U32>, rest: List<&2, U32>, params: List<&2, List<&2, U32>>, body: List<&2, Bl>, +no: U32, +ind: U32, +what: U32}
  NObj{+abs: Bool, +ext: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, kids: List<&2, Node>, +no: U32}
  NBad{txt: List<&2, U32>, +no: U32}
  NErr{msg: List<&2, U32>, +no: U32}
  NBend{lines: List<&2, Ln>, +no: U32}

# an object being read: its header and its members so far, reversed; the
# module is the frame at the stack's bottom, never closed
type Fr is Data:
  Fr{+top: Bool, +ind: U32, +abs: Bool, +with: Bool, +ext: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, kids: List<&2, Node>, +no: U32}

def fr.add(f: Fr, n: Node) -> Fr:
  match f:
    case Fr{+top, +ind, +abs, +with, +ext, name, parents, kids, +no}:
      Fr{top, ind, abs, with, ext, name, parents, Con{n, kids}, no}

def close.into(st: List<&2, Fr>, n: Node) -> List<&2, Fr>:
  match st:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      Con{fr.add(f, n), rest}

# an object with members whose header leaves out `with`: an error there
def close.with(+with: Bool, kids: List<&2, Node>, +name: List<&2, U32>, +no: U32, st: List<&2, Fr>) -> List<&2, Fr>:
  match with kids:
    case False{} Con{k, t}:
      close.into(st, NErr{List.append(&2, U32, codes("object "), List.append(&2, U32, name,
        codes(" has members, so its header ends with `with`"))), no})
    case _ _:
      st

# objects closed while the top one starts at or right of column i; fuel,
# the stack's height
def close.go(n: Nat, st: List<&2, Fr>, +i: U32) -> List<&2, Fr>:
  match n:
    case 0n:
      st
    case 1n++k:
      match st:
        case Nil{}:
          Nil{}
        case Con{f, +rest}:
          match f:
            case Fr{+top, +ind, +abs, +with, +ext, +name, +parents, +kids, +no}:
              when(List<&2, Fr>, Bool.not(top) && U32.is_ge(ind, i),
                u => close.go(k, close.into(close.with(with, kids, name, no, rest), NObj{abs, ext, name, parents, List.reverse(&2, Node, kids), no}), i),
                u => Con{Fr{top, ind, abs, with, ext, name, parents, kids, no}, rest})

def close(+st: List<&2, Fr>, +i: U32) -> List<&2, Fr>:
  close.go(List.length(&2, Fr, st), st, i)

def item.ind(it: Item) -> U32 & Item:
  match it:
    case IImport{txt, +no, +ind}:
      (ind, IImport{txt, no, ind})
    case IObj{+abs, +with, +ext, name, parents, +no, +ind}:
      (ind, IObj{abs, with, ext, name, parents, no, ind})
    case IDecl{names, +no, +ind}:
      (ind, IDecl{names, no, ind})
    case IDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      (ind, IDef{share, upd, name, rest, params, body, no, ind, what})
    case IBad{txt, +no, +ind}:
      (ind, IBad{txt, no, ind})
    case IBend{lines, +no, +ind}:
      (ind, IBend{lines, no, ind})

def tree.put(st: List<&2, Fr>, it: Item) -> List<&2, Fr>:
  match it:
    case IImport{txt, +no, +ind}:
      close.into(st, NImport{txt, no})
    case IObj{+abs, +with, +ext, name, parents, +no, +ind}:
      Con{Fr{False{}, ind, abs, with, ext, name, parents, Nil{}, no}, st}
    case IDecl{names, +no, +ind}:
      close.into(st, NDecl{names, no})
    case IDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      close.into(st, NDef{share, upd, name, rest, params, toks.lines(body), no, ind, what})
    case IBad{txt, +no, +ind}:
      close.into(st, NBad{txt, no})
    case IBend{lines, +no, +ind}:
      close.into(st, NBend{lines, no})

def tree.item(r: U32 & Item, st: List<&2, Fr>) -> List<&2, Fr>:
  (+i, it) = r
  tree.put(close(st, i), it)

def tree.go(its: List<&2, Item>, st: List<&2, Fr>) -> List<&2, Fr>:
  match its:
    case Nil{}:
      close(st, 0)
    case Con{it, t}:
      tree.go(t, tree.item(item.ind(it), st))

def tree.fin(st: List<&2, Fr>) -> List<&2, Node>:
  match st:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      match f:
        case Fr{+top, +ind, +abs, +with, +ext, name, parents, kids, +no}:
          List.reverse(&2, Node, kids)

# the module's members, its objects nested
def tree(its: List<&2, Item>) -> List<&2, Node>:
  tree.fin(tree.go(its, [Fr{True{}, 0, False{}, True{}, False{}, Nil{}, Nil{}, Nil{}, 0}]))

def read.at(bs: List<&2, U32>, +base: U32) -> List<&2, Node>:
  tree(flat(lines.at(bs, base)))

def read(bs: List<&2, U32>) -> List<&2, Node>:
  read.at(bs, 0)

# The structure, printed
# ======================

def show.names(ns: List<&2, List<&2, U32>>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      match t:
        case Nil{}:
          text(n)
        case Con{h, r}:
          text(n) ++ ", " ++ show.names(Con{h, r})

def show.share(+s: U32) -> String:
  match s:
    case 1:
      "shared "
    case 2:
      "copied "
    case _:
      ""

def show.kw(+u: Bool) -> String:
  match u:
    case True{}:
      "upd "
    case False{}:
      "def "

def show.abs(+a: Bool) -> String:
  match a:
    case True{}:
      "abstract object "
    case False{}:
      "object "

def show.ext(ps: List<&2, List<&2, U32>>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      " extends " ++ show.names(Con{p, t})

# the names a body's tokens hold, in order, as found
def show.toks(ts: List<&2, Tok>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      rest
    case Con{tk, t}:
      match tk:
        case TName{txt}:
          Con{txt, show.toks(t, rest)}
        case _:
          show.toks(t, rest)

def show.uses(bs: List<&2, Bl>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          show.toks(ts, show.uses(t))

def show.used(ns: List<&2, List<&2, U32>>, ind: String) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      ind ++ "  uses " ++ show.names(Con{n, t}) ++ "\n"

def show.first(ls: List<&2, Ln>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, txt}:
          text(txt)

def show.line(+no: U32) -> String:
  "  (line " ++ U32.show(no) ++ ")"

# the tree, an item a line, members indented under their object; fuel,
# the items' count, as the walk enters a member list from its object
def show.go(n: Nat, ns: List<&2, Node>, +ind: String) -> String:
  match n:
    case 0n:
      ""
    case 1n++k:
      match ns:
        case Nil{}:
          ""
        case Con{nd, t}:
          match nd:
            case NImport{txt, +no}:
              ind ++ text(txt) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NDecl{names, +no}:
              ind ++ "declare " ++ show.names(names) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NDef{+share, +upd, name, rest, params, +body, +no, +dind, +what}:
              ind ++ show.share(share) ++ show.kw(upd) ++ text(name) ++ " [" ++ show.names(params) ++ "], " ++
                U32.show(U32.from_nat(List.length(&2, Bl, body))) ++ " body lines" ++ show.line(no) ++ "\n" ++
                show.used(show.uses(body), ind) ++ show.go(k, t, ind)
            case NObj{+abs, +ext, name, parents, kids, +no}:
              ind ++ show.abs(abs) ++ text(name) ++ show.ext(parents) ++ show.line(no) ++ "\n" ++
                show.go(k, kids, ind ++ "  ") ++ show.go(k, t, ind)
            case NBad{txt, +no}:
              ind ++ "? " ++ text(txt) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NErr{msg, +no}:
              ind ++ "! " ++ text(msg) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NBend{lines, +no}:
              ind ++ "Bend's " ++ show.first(lines) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)

def show(ns: List<&2, Node>, +n: Nat) -> String:
  show.go(n, ns, "")

# Objects
# =======
#
# The module and its objects, numbered in source order, the module 0.
# The module is no object (`blend-module-is-bend`): it holds Bend's
# definitions, its imports and its objects, and carries number 0 for
# their checks alone. Each object's parents found by name, its linearization by C3 as glam
# linearizes, and the definitions each has by applying the members of its
# linearization from the last, its base, to itself (`blend-objects`).
# Errors are found per object, each reported once: where an object's
# error is its parent's already, the parent's report stands.

def has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      U32.is_eq(h, x) || has(t, x)

def names.eq(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      same(x, y) && names.eq(xt, yt)
    case _ _:
      False{}

def blank.parts(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      False{}

def List.head.or(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x

def names.has(ns: List<&2, List<&2, U32>>, +n: List<&2, U32>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{x, t}:
      same(x, n) || names.has(t, n)

# a dot told by a test, not a byte's match, so that a law can follow it
# (blend/LAWS.bend, `names.dots_parts`)
def parts.go(xs: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, Con{List.reverse(&2, U32, cur), out})
    case Con{+h, +t}:
      when(List<&2, List<&2, U32>>, U32.is_eq(h, 46), u => parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out}),
        u => parts.go(t, Con{h, cur}, out))

# a dotted name's parts
def parts(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  parts.go(xs, Nil{}, Nil{})

# an object: its number, its host's, its path from the module, its
# parents as written, its members (the module, number 0: the whole file)
type Ob is Data:
  Ob{+id: U32, +host: U32, path: List<&2, List<&2, U32>>, +abs: Bool, parents: List<&2, List<&2, U32>>, mems: List<&2, Node>, +no: U32, +kind: U32, +tpl: U32}

# an object's kind: 0 a top-level object (or a module's root), 1 a nested
# object as written, 2 an extension, `extend N with` (both mixins, never
# emitted nor named by path: Nested objects, below), 3 a nested object
# made for its host. Its tpl, the mixin as written a bound mixin copies
# (a copy's host the one it is bound to), else its own number
def ob.kind.of(+ext: Bool, +path: List<&2, List<&2, U32>>) -> U32:
  when(U32, ext, u => 2, u => when(U32, blank.parts(path), v => 0, v => 1))

# a member list being walked, with its object's number and path
type Wf is Data:
  Wf{+host: U32, path: List<&2, List<&2, U32>>, nodes: List<&2, Node>}

def count(ns: List<&2, Node>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{nd, t}:
      match nd:
        case NObj{+abs, +ext, name, parents, kids, +no}:
          1n+Nat.add(count(kids), count(t))
        case _:
          1n+count(t)

# the objects in source order, an object entered as it is met; fuel: a
# node or a finished member list a step
def obs.go(n: Nat, st: List<&2, Wf>, +next: U32, out: List<&2, Ob>) -> List<&2, Ob>:
  match n:
    case 0n:
      out
    case 1n+k:
      match st:
        case Nil{}:
          out
        case Con{f, rest}:
          match f:
            case Wf{+host, +path, nodes}:
              match nodes:
                case Nil{}:
                  obs.go(k, rest, next, out)
                case Con{nd, t}:
                  match nd:
                    case NObj{+abs, +ext, +name, parents, +kids, +no}:
                      obs.go(k, Con{Wf{next, List.append(&2, List<&2, U32>, path, [name]), kids}, Con{Wf{host, path, t}, rest}},
                        (next + 1 : U32), Con{Ob{next, host, List.append(&2, List<&2, U32>, path, [name]), abs, parents, kids, no, ob.kind.of(ext, path), next}, out})
                    case _:
                      obs.go(k, Con{Wf{host, path, t}, rest}, next, out)

# a module's objects after those before it, reversed: its root, numbered
# next, its own host (the module is no object, `blend-module-is-bend`),
# then its objects
def obs.mod(+tree: List<&2, Node>, +k: U32, +out: List<&2, Ob>) -> List<&2, Ob>:
  obs.go(Nat.add(Nat.add(count(tree), count(tree)), 2n), [Wf{U32.from_nat(List.length(&2, Ob, out)), Nil{}, tree}],
    (U32.from_nat(List.length(&2, Ob, out)) + 1 : U32),
    Con{Ob{U32.from_nat(List.length(&2, Ob, out)), U32.from_nat(List.length(&2, Ob, out)), Nil{}, False{}, Nil{}, tree, (k * 1000000 : U32), 0,
      U32.from_nat(List.length(&2, Ob, out))}, out})

def obs.mods(ts: List<&2, List<&2, Node>>, +k: U32, +out: List<&2, Ob>) -> List<&2, Ob>:
  match ts:
    case Nil{}:
      out
    case Con{tr, t}:
      obs.mods(t, (k + 1 : U32), obs.mod(tr, k, out))

# every module's objects, the root's first, numbered in order
def obs(+trees: List<&2, List<&2, Node>>) -> List<&2, Ob>:
  List.reverse(&2, Ob, obs.mods(trees, 0, Nil{}))

def ob.or(m: Maybe<&2, Ob>) -> Ob:
  match m:
    case None{}:
      Ob{0, 0, Nil{}, False{}, Nil{}, Nil{}, 0, 0, 0}
    case Some{o}:
      o

def ob.at(+obs: List<&2, Ob>, +id: U32) -> Ob:
  ob.or(List.get(&2, Ob, obs, U32.to_nat(id)))

def ob.path(o: Ob) -> List<&2, List<&2, U32>>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      path

def ob.host(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      host

def ob.abs(o: Ob) -> Bool:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      abs

def ob.no(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      no

def ob.mems(o: Ob) -> List<&2, Node>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      mems

def dots(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match t:
        case Nil{}:
          p
        case Con{h, r}:
          List.append(&2, U32, p, Con{46, dots(Con{h, r})})

def ob.name.of(+path: List<&2, List<&2, U32>>) -> String:
  match path:
    case Nil{}:
      "the module"
    case Con{h, t}:
      text(dots(Con{h, t}))

# an object's name as messages give it; the module's, "the module"
def ob.name(+obs: List<&2, Ob>, +id: U32) -> String:
  ob.name.of(ob.path(ob.at(obs, id)))

# whether an object of this kind is one, not a mixin
def is.object(+kind: U32) -> Bool:
  U32.is_eq(kind, 0) || U32.is_eq(kind, 3)

def ob.tpl(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      tpl

# whether an object is a mixin as written (not a bound copy of one)
def is.written(+obs: List<&2, Ob>, +id: U32) -> Bool:
  U32.is_eq(ob.tpl(ob.at(obs, id)), id)

def ob.kind(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      kind

def path.last(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  on.maybe(List<&2, U32>, List<&2, U32>, List.last(&2, List<&2, U32>, ps), u => Nil{}, x => x)

# an object's name as a message of two objects gives it: a bound copy,
# the nested object it serves (`Outer2.Inner`)
def ob.say(+obs: List<&2, Ob>, +id: U32) -> String:
  when(String, Bool.not(is.object(ob.kind(ob.at(obs, id)))) && Bool.not(is.written(obs, id)),
    u => ob.name.of(List.append(&2, List<&2, U32>, ob.path(ob.at(obs, ob.host(ob.at(obs, id)))), [path.last(ob.path(ob.at(obs, id)))])),
    u => ob.name(obs, id))

def loc.mod(+no: U32) -> U32:
  (no / 1000000 : U32)

# the first object at path p
# the first object of module m at path p
def find.path(+obs: List<&2, Ob>, +m: U32, +p: List<&2, List<&2, U32>>) -> Maybe<&2, U32>:
  match obs:
    case Nil{}:
      None{}
    case Con{+o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(Maybe<&2, U32>, names.eq(path, p) && U32.is_eq(loc.mod(no), m) && is.object(kind), u => Some{id}, u => find.path(t, m, p))

# whether id is a module's root
def is.root(+obs: List<&2, Ob>, +id: U32) -> Bool:
  U32.is_eq(ob.host(ob.at(obs, id)), id)

# an import's alias, `M` of `import ./m.blend as M`: the importing
# module's root, and the imported's
type Al is Data:
  Al{name: List<&2, U32>, +from: U32, +to: U32, +no: U32}

def al.find(als: List<&2, Al>, +from: U32, +n: List<&2, U32>) -> Maybe<&2, U32>:
  match als:
    case Nil{}:
      None{}
    case Con{a, t}:
      match a:
        case Al{+name, +f, +to, +no}:
          when(Maybe<&2, U32>, U32.is_eq(f, from) && same(name, n), u => Some{to}, u => al.find(t, from, n))

# an object's name found from scope s outward to its module: the object
# at s's path and the name's parts, in s's module; at the module, a name
# whose first part is an import's alias found in the module imported;
# fuel, the objects' count
def resolve(n: Nat, +als: List<&2, Al>, +obs: List<&2, Ob>, +s: U32, +segs: List<&2, List<&2, U32>>) -> Maybe<&2, U32>:
  match n:
    case 0n:
      None{}
    case 1n++k:
      on.maybe(U32, Maybe<&2, U32>, find.path(obs, loc.mod(ob.no(ob.at(obs, s))), List.append(&2, List<&2, U32>, ob.path(ob.at(obs, s)), segs)),
        u => when(Maybe<&2, U32>, is.root(obs, s),
          v => on.maybe(U32, Maybe<&2, U32>, al.find(als, s, List.head.or(segs)), w => None{},
            +to => when(Maybe<&2, U32>, blank.parts(List.tail(&2, List<&2, U32>, segs)), w => None{},
              w => resolve(k, als, obs, to, List.tail(&2, List<&2, U32>, segs)))),
          v => resolve(k, als, obs, ob.host(ob.at(obs, s)), segs)),
        x => Some{x})

def parent.find(+als: List<&2, Al>, +obs: List<&2, Ob>, +host: U32, +p: List<&2, U32>) -> Maybe<&2, U32>:
  resolve(List.length(&2, Ob, obs), als, obs, host, parts(p))

# an object's parents found, those named by nothing left out
def pids.go(ps: List<&2, List<&2, U32>>, +als: List<&2, Al>, +obs: List<&2, Ob>, +host: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      on.maybe(U32, List<&2, U32>, parent.find(als, obs, host, p), u => pids.go(t, als, obs, host), x => Con{x, pids.go(t, als, obs, host)})

# xs, each kept where it first appears
def uniq(xs: List<&2, U32>, +seen: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, has(seen, x), u => uniq(t, seen), u => Con{x, uniq(t, Con{x, seen})})

# the mixins as written named n whose host is q
def mixins.in(os: List<&2, Ob>, +q: U32, +n: List<&2, U32>) -> List<&2, U32>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, U32>, U32.is_eq(host, q) && Bool.not(is.object(kind)) && U32.is_eq(tpl, id) && same(path.last(path), n),
            u => Con{id, mixins.in(t, q, n)}, u => mixins.in(t, q, n))

# the mixins named n of the objects in a linearization, in its order
def mixins.of(qs: List<&2, U32>, +obs: List<&2, Ob>, +n: List<&2, U32>) -> List<&2, U32>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      List.append(&2, U32, mixins.in(obs, ob.tpl(ob.at(obs, q)), n), mixins.of(t, obs, n))

# a linearization found: whether it is sound (its parents' too), and its order
type Lz is Data:
  Lz{+ok: Bool, ord: List<&2, U32>}

def lz.or(m: Maybe<&2, Maybe<&2, Lz>>) -> Maybe<&2, Lz>:
  match m:
    case None{}:
      None{}
    case Some{z}:
      z

def lz.at(+lins: List<&2, Maybe<&2, Lz>>, +id: U32) -> Maybe<&2, Lz>:
  lz.or(List.get(&2, Maybe<&2, Lz>, lins, U32.to_nat(id)))

def lz.ord(m: Maybe<&2, Lz>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          ord

def ob.parents(o: Ob) -> List<&2, List<&2, U32>>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      parents

def last.id(xs: List<&2, U32>) -> Maybe<&2, U32>:
  List.last(&2, U32, xs)

# the parents the mixin introducing a nested object names, found from the
# host it is made for: a bare name binds as a body's would, so that
# `object Sub extends In`, made for Outer2, extends Outer2.In
def intro.parents(+chain: List<&2, U32>, +als: List<&2, Al>, +obs: List<&2, Ob>, +x: U32) -> List<&2, U32>:
  on.maybe(U32, List<&2, U32>, last.id(chain), u => Nil{}, +i => uniq(pids.go(ob.parents(ob.at(obs, i)), als, obs, x), Nil{}))

# the copy of mixin t bound to x, if made
def copy.find(os: List<&2, Ob>, +t: U32, +x: U32) -> Maybe<&2, U32>:
  match os:
    case Nil{}:
      None{}
    case Con{o, +r}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          when(Maybe<&2, U32>, U32.is_eq(tpl, t) && U32.is_eq(host, x) && Bool.not(U32.is_eq(id, t)), u => Some{id}, u => copy.find(r, t, x))

# the copies bound to x of mixins ts, those made so far
def copies.for(ts: List<&2, U32>, +obs: List<&2, Ob>, +x: U32) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      on.maybe(U32, List<&2, U32>, copy.find(obs, t, x), u => copies.for(r, obs, x), +c => Con{c, copies.for(r, obs, x)})

# a parent named twice is one parent. A nested object made for host x has
# x's mixins of its name, down x's linearization as last found, then the
# parents of the one introducing it, found from x (Nested objects, below);
# a mixin, none of its own
def pids.of(o: Ob, +als: List<&2, Al>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>) -> List<&2, U32>:
  match o:
    case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
      match kind:
        case 3:
          List.append(&2, U32, copies.for(mixins.of(lz.ord(lz.at(ls, host)), obs, path.last(path)), obs, host),
            intro.parents(mixins.of(lz.ord(lz.at(ls, host)), obs, path.last(path)), als, obs, host))
        case 0:
          uniq(pids.go(parents, als, obs, host), Nil{})
        case _:
          Nil{}

# each object's parents, by number
def pids(os: List<&2, Ob>, +als: List<&2, Al>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>) -> List<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{pids.of(o, als, obs, ls), pids(t, als, obs, ls)}

# an error: its line and its message
type Er is Data:
  Er{+no: U32, msg: String}

def er.le(a: Er, b: Er) -> Bool:
  match a b:
    case Er{+x, m} Er{+y, n}:
      U32.is_le(x, y)

def er.parents(ps: List<&2, List<&2, U32>>, +als: List<&2, Al>, +obs: List<&2, Ob>, +id: U32, +host: U32, +no: U32) -> List<&2, Er>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      on.maybe(U32, List<&2, Er>, parent.find(als, obs, host, p),
        u => Con{Er{no, ob.name(obs, id) ++ " extends " ++ text(p) ++ ", which names no object"}, er.parents(t, als, obs, id, host, no)},
        x => er.parents(t, als, obs, id, host, no))

# a mixin of host's named n and of the kind given, other than id
def mixin.other(os: List<&2, Ob>, +id: U32, +host: U32, +n: List<&2, U32>, +k: U32) -> Maybe<&2, U32>:
  match os:
    case Nil{}:
      None{}
    case Con{o, +t}:
      match o:
        case Ob{+x, +h, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(Maybe<&2, U32>, U32.is_eq(h, host) && U32.is_eq(kind, k) && Bool.not(U32.is_eq(x, id)) && U32.is_eq(tpl, x) && same(path.last(path), n),
            u => Some{x}, u => mixin.other(t, id, host, n, k))

def loc.line(+no: U32) -> U32:
  (no % 1000000 : U32)

def er.twice.k(+obs: List<&2, Ob>, +id: U32, +x: U32, +no: U32) -> List<&2, Er>:
  when(List<&2, Er>, U32.is_lt(x, id), v => [Er{no, "object " ++ ob.name(obs, id) ++ " is defined at line " ++ U32.show(loc.line(ob.no(ob.at(obs, x)))) ++ " already"}],
    v => Nil{})

def er.twice.top(+obs: List<&2, Ob>, +id: U32, +path: List<&2, List<&2, U32>>, +no: U32) -> List<&2, Er>:
  on.maybe(U32, List<&2, Er>, find.path(obs, loc.mod(no), path), u => Nil{},
    +x => when(List<&2, Er>, U32.is_eq(x, id), v => Nil{},
      v => [Er{no, "object " ++ ob.name(obs, id) ++ " is defined at line " ++ U32.show(ob.no(ob.at(obs, x))) ++ " already"}]))

def er.twice(+obs: List<&2, Ob>, +id: U32, +path: List<&2, List<&2, U32>>, +no: U32, +kind: U32, +host: U32) -> List<&2, Er>:
  match kind:
    case 0:
      er.twice.top(obs, id, path, no)
    case 3:
      Nil{}
    case _:
      on.maybe(U32, List<&2, Er>, mixin.other(obs, id, host, path.last(path), kind), u => Nil{}, +x => er.twice.k(obs, id, x, no))

# Import paths, as Bend's (tried 2026-11-05): `./` and `../` leading
# only, then names of letters, digits, `_` and `-`, the last the file's
# with its extension; no absolute path, no `.` or `..` after a name, no
# empty part between names.

def ch.plain(+c: U32) -> Bool:
  (U32.is_gt(c, 47) && U32.is_lt(c, 58)) || (U32.is_gt(c, 64) && U32.is_lt(c, 91)) || (U32.is_gt(c, 96) && U32.is_lt(c, 123)) ||
    U32.is_eq(c, 95) || U32.is_eq(c, 45)

def chars.plain(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      ch.plain(c) && chars.plain(t)

def part.plain(+s: List<&2, U32>) -> Bool:
  Bool.not(List.is_empty(&2, U32, s)) && chars.plain(s)

def ends(+xs: List<&2, U32>, +p: List<&2, U32>) -> Bool:
  starts(List.reverse(&2, U32, xs), List.reverse(&2, U32, p))

# the names after the leading part, the last with its extension
def parts.plain(ss: List<&2, List<&2, U32>>, +ext: List<&2, U32>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{+s, +t}:
      match t:
        case Nil{}:
          ends(s, ext) && part.plain(List.take(&2, U32, s, Nat.sub(List.length(&2, U32, s), List.length(&2, U32, ext))))
        case Con{x, r}:
          part.plain(s) && parts.plain(t, ext)

def parts.lead(ss: List<&2, List<&2, U32>>, +ext: List<&2, U32>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{+s, +t}:
      when(Bool, same(s, codes(".")) || same(s, codes("..")) || List.is_empty(&2, U32, s), u => parts.lead(t, ext), u => parts.plain(Con{s, t}, ext))

def split.slash(xs: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, Con{List.reverse(&2, U32, cur), out})
    case Con{+h, t}:
      match h:
        case 47:
          split.slash(t, Nil{}, Con{List.reverse(&2, U32, cur), out})
        case _:
          split.slash(t, Con{h, cur}, out)

def import.parts(ss: List<&2, List<&2, U32>>, +ext: List<&2, U32>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{+s, +t}:
      when(Bool, List.is_empty(&2, U32, s), u => False{},
        u => when(Bool, same(s, codes(".")) || same(s, codes("..")), v => parts.lead(t, ext), v => parts.plain(Con{s, t}, ext)))

def import.plain(+p: List<&2, U32>, +ext: List<&2, U32>) -> Bool:
  import.parts(split.slash(p, Nil{}, Nil{}), ext)

# an import: its path as written, its alias, whether it is Blend's
type Im is Data:
  Im{path: List<&2, U32>, alias: List<&2, U32>, +blend: Bool, +no: U32}

def im.plain.ers(i: Im) -> List<&2, Er>:
  match i:
    case Im{+path, alias, +blend, +no}:
      when(List<&2, Er>, blend && Bool.not(import.plain(path, codes(".blend"))),
        u => [Er{no, "import " ++ text(path) ++ ": an import path is plain names, letters, digits, _ and -, with ./ and ../ leading only, as Bend's"}],
        u => Nil{})

def im.made(r: List<&2, U32> & List<&2, U32>, +no: U32) -> Maybe<&2, Im>:
  (+path, +rest) = r
  when(Maybe<&2, Im>, starts(rest, codes("as ")) && name.ok(trim(drop(3n, rest))),
    u => Some{Im{path, trim(drop(3n, rest)), ends(path, codes(".blend")), no}}, u => None{})

# `import PATH as ALIAS`; Bend's other forms (by a package's hash or name)
# are Bend's alone
def im.of(+txt: List<&2, U32>, +no: U32) -> Maybe<&2, Im>:
  im.made(until(drop(7n, txt), 32), no)

# a member list's lines Blend cannot read, and imports inside an object
def er.mems(ns: List<&2, Node>, +top: Bool) -> List<&2, Er>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, +t}:
      match nd:
        case NBad{+txt, +no}:
          Con{Er{no, when(String, starts(txt, codes("upd law ")),
            u => "a law is stated once, never updated: state a new law, or update its proof (upd proof)",
            u => when(String, starts(txt, codes("declare ")) && holds(txt, codes("(")),
              v => text(txt) ++ ": a typed declaration states its parameters and what it returns, `declare def f(params) -> T`",
              v => "Blend cannot read this line: " ++ text(txt)))}, er.mems(t, top)}
        case NErr{msg, +no}:
          Con{Er{no, text(msg)}, er.mems(t, top)}
        case NBend{lines, +no}:
          when(List<&2, Er>, top, u => er.mems(t, top),
            u => Con{Er{no, "a datatype belongs to the module; an object's types are members, `type S = ...`"}, er.mems(t, top)})
        case NImport{txt, +no}:
          when(List<&2, Er>, top, u => er.mems(t, top),
            u => Con{Er{no, "an import belongs to the module, outside every object"}, er.mems(t, top)})
        case NDef{+share, +upd, +name, rest, params, body, +no, +ind, +what}:
          when(List<&2, Er>, top && Bool.not(U32.is_eq(share, 0)),
            u => Con{Er{no, show.share(share) ++ "def " ++ text(name) ++ ": the module is no object; its definitions are Bend's, shared as Bend shares them"},
              er.mems(t, top)},
            u => er.mems(t, top))
        case NDecl{names, +no}:
          when(List<&2, Er>, top,
            u => Con{Er{no, "declare " ++ show.names(names) ++ ": the module is no object; declare names in an abstract object"}, er.mems(t, top)},
            u => er.mems(t, top))
        case _:
          er.mems(t, top)

# an extension at the top level, or one naming parents: a mixin on the
# nested object its host has (blend-namespaces-as-bends)
def er.ext(+obs: List<&2, Ob>, +id: U32, +host: U32, +path: List<&2, List<&2, U32>>, ps: List<&2, List<&2, U32>>, +no: U32, +kind: U32) -> List<&2, Er>:
  when(List<&2, Er>, Bool.not(U32.is_eq(kind, 2)), u => Nil{},
    u => when(List<&2, Er>, is.root(obs, host),
      v => [Er{no, "extend " ++ text(path.last(path)) ++ ": an extension is a mixin on a nested object, and stays out of the top level"}],
      v => when(List<&2, Er>, blank.parts(ps), w => Nil{},
        w => [Er{no, "extend " ++ text(path.last(path)) ++ ": an extension keeps its object's parents, and names none"}])))

# each object's errors of reading and naming
def er.obs(os: List<&2, Ob>, +als: List<&2, Al>, +obs: List<&2, Ob>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      match o:
        case Ob{+id, +host, +path, +abs, +parents, mems, +no, +kind, +tpl}:
          List.append(&2, Er, when(List<&2, Er>, U32.is_eq(tpl, id), u => er.mems(mems, U32.is_eq(id, host)), u => Nil{}),
            List.append(&2, Er, when(List<&2, Er>, U32.is_eq(id, host) || Bool.not(U32.is_eq(tpl, id)), u => Nil{}, u => er.twice(obs, id, path, no, kind, host)),
              List.append(&2, Er, when(List<&2, Er>, U32.is_eq(tpl, id), u => er.ext(obs, id, host, path, parents, no, kind), u => Nil{}),
                List.append(&2, Er, when(List<&2, Er>, U32.is_eq(kind, 0), u => er.parents(parents, als, obs, id, host, no), u => Nil{}),
                  er.obs(t, als, obs)))))

# C3
# --
#
# An object's linearization is itself, then the merge of its parents'
# linearizations and its parents' list: each turn takes the first head
# that is in no list's tail. The lists keep their owners, for the message
# when no head is free.

type Sq is Data:
  Sq{+owner: U32, xs: List<&2, U32>}

def in_tails(ss: List<&2, Sq>, +h: U32) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          match xs:
            case Nil{}:
              in_tails(t, h)
            case Con{x, r}:
              has(r, h) || in_tails(t, h)

# the first head in no tail
def c3.good(cs: List<&2, Sq>, +all: List<&2, Sq>) -> Maybe<&2, U32>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Sq{+o, xs}:
          match xs:
            case Nil{}:
              c3.good(t, all)
            case Con{+h, r}:
              when(Maybe<&2, U32>, in_tails(all, h), u => c3.good(t, all), u => Some{h})

def c3.head.drop(xs: List<&2, U32>, +h: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, U32.is_eq(x, h), u => t, u => Con{x, t})

def c3.keep(+o: U32, xs: List<&2, U32>, rest: List<&2, Sq>) -> List<&2, Sq>:
  match xs:
    case Nil{}:
      rest
    case Con{x, r}:
      Con{Sq{o, Con{x, r}}, rest}

# the lists, h taken from their heads, the empty ones dropped
def c3.take(ss: List<&2, Sq>, +h: U32) -> List<&2, Sq>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          c3.keep(o, c3.head.drop(xs, h), c3.take(t, h))

type Mg is Data:
  MOk{ord: List<&2, U32>}
  MFail{seqs: List<&2, Sq>}

# fuel: the lists' lengths, a head taken each turn
def c3.merge(n: Nat, +seqs: List<&2, Sq>, +out: List<&2, U32>) -> Mg:
  match n:
    case 0n:
      MFail{seqs}
    case 1n++k:
      match seqs:
        case Nil{}:
          MOk{List.reverse(&2, U32, out)}
        case Con{+s, +t}:
          on.maybe(U32, Mg, c3.good(Con{s, t}, Con{s, t}), u => MFail{Con{s, t}},
            +h => c3.merge(k, c3.take(Con{s, t}, h), Con{h, out}))

def sqs.len(ss: List<&2, Sq>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          Nat.add(List.length(&2, U32, xs), sqs.len(t))

def lin.seqs.k(+ok: Bool, +p: U32, ord: List<&2, U32>, rest: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match ok:
    case True{}:
      match rest:
        case None{}:
          None{}
        case Some{r}:
          match r:
            case Some{ss}:
              Some{Some{Con{Sq{p, ord}, ss}}}
            case None{}:
              Some{None{}}
    case False{}:
      match rest:
        case None{}:
          None{}
        case Some{r}:
          Some{None{}}

def lin.seqs.z(+p: U32, m: Maybe<&2, Lz>, rest: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match m:
    case None{}:
      None{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          lin.seqs.k(ok, p, ord, rest)

# the parents' linearizations as lists to merge, None while one is missing
# (an unsound one: Some of None, its error its own)
def lin.seqs(ps: List<&2, U32>, +lins: List<&2, Maybe<&2, Lz>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match ps:
    case Nil{}:
      Some{Some{Nil{}}}
    case Con{+p, t}:
      lin.seqs.z(p, lz.at(lins, p), lin.seqs(t, lins))

def lin.mg(+id: U32, m: Mg) -> Lz:
  match m:
    case MOk{ord}:
      Lz{True{}, Con{id, ord}}
    case MFail{ss}:
      Lz{False{}, [id]}

def lin.of(+id: U32, +ps: List<&2, U32>, ss: Maybe<&2, List<&2, Sq>>) -> Lz:
  match ss:
    case None{}:
      Lz{False{}, [id]}
    case Some{+seqs}:
      lin.mg(id, c3.merge(1n+sqs.len(List.append(&2, Sq, seqs, [Sq{id, ps}])), c3.take(List.append(&2, Sq, seqs, [Sq{id, ps}]), 4294967295), Nil{}))

def lin.try(+id: U32, +ps: List<&2, U32>, m: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Lz>:
  match m:
    case None{}:
      None{}
    case Some{ss}:
      Some{lin.of(id, ps, ss)}

# a round: each object not yet linearized whose parents are
def lin.round(ps: List<&2, List<&2, U32>>, cur: List<&2, Maybe<&2, Lz>>, +id: U32, +all: List<&2, Maybe<&2, Lz>>) -> List<&2, Maybe<&2, Lz>>:
  match ps cur:
    case Con{+p, pt} Con{c, ct}:
      match c:
        case Some{z}:
          Con{Some{z}, lin.round(pt, ct, (id + 1 : U32), all)}
        case None{}:
          Con{lin.try(id, p, lin.seqs(p, all)), lin.round(pt, ct, (id + 1 : U32), all)}
    case _ _:
      Nil{}

def lin.go(n: Nat, +pss: List<&2, List<&2, U32>>, +lins: List<&2, Maybe<&2, Lz>>) -> List<&2, Maybe<&2, Lz>>:
  match n:
    case 0n:
      lins
    case 1n+k:
      lin.go(k, pss, lin.round(pss, lins, 0, lins))

def nones(ps: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Lz>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{None{}, nones(t)}

# every object's linearization, None where its parents lead back to it;
# a round for each object at most, as each round linearizes one at least
def lins(+pss: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Lz>>:
  lin.go(1n+List.length(&2, List<&2, U32>, pss), pss, nones(pss))

# two lists that order two heads both ways, for the message
type Cf is Data:
  Cf{+a: U32, +x: U32, +b: U32, +y: U32}

def cf.with(ss: List<&2, Sq>, +a: U32, +x: U32, +r: List<&2, U32>) -> Maybe<&2, Cf>:
  match ss:
    case Nil{}:
      None{}
    case Con{s, t}:
      match s:
        case Sq{+b, xs}:
          match xs:
            case Nil{}:
              cf.with(t, a, x, r)
            case Con{+y, +r2}:
              when(Maybe<&2, Cf>, has(r2, x) && has(r, y), u => Some{Cf{a, x, b, y}}, u => cf.with(t, a, x, r))

def cf.find(cs: List<&2, Sq>, +all: List<&2, Sq>) -> Maybe<&2, Cf>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Sq{+a, xs}:
          match xs:
            case Nil{}:
              cf.find(t, all)
            case Con{+x, +r}:
              on.maybe(Cf, Maybe<&2, Cf>, cf.with(all, a, x, r), u => cf.find(t, all), f => Some{f})

def cf.msg(+obs: List<&2, Ob>, m: Maybe<&2, Cf>) -> String:
  match m:
    case None{}:
      "no order fits its parents' orders"
    case Some{f}:
      match f:
        case Cf{+a, +x, +b, +y}:
          ob.name(obs, a) ++ " puts " ++ ob.name(obs, x) ++ " before " ++ ob.name(obs, y) ++ ", and " ++
            ob.name(obs, b) ++ " puts " ++ ob.name(obs, y) ++ " before " ++ ob.name(obs, x)

def c3.why(+obs: List<&2, Ob>, +id: U32, m: Mg) -> List<&2, Er>:
  match m:
    case MOk{ord}:
      Nil{}
    case MFail{+ss}:
      [Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " has no C3 linearization: " ++ cf.msg(obs, cf.find(ss, ss))}]

def c3.er(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, ss: Maybe<&2, List<&2, Sq>>) -> List<&2, Er>:
  match ss:
    case None{}:
      Nil{}
    case Some{+seqs}:
      c3.why(obs, id, c3.merge(1n+sqs.len(List.append(&2, Sq, seqs, [Sq{id, ps}])), c3.take(List.append(&2, Sq, seqs, [Sq{id, ps}]), 4294967295), Nil{}))

def c3.er.k(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, m: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> List<&2, Er>:
  match m:
    case None{}:
      Nil{}
    case Some{ss}:
      c3.er(obs, id, ps, ss)

# the linearization errors: an object its parents lead back to, and one
# whose sound parents have no merge
def er.lins(ps: List<&2, List<&2, U32>>, ls: List<&2, Maybe<&2, Lz>>, +id: U32, +obs: List<&2, Ob>, +all: List<&2, Maybe<&2, Lz>>) -> List<&2, Er>:
  match ps ls:
    case Con{+p, +pt} Con{l, +lt}:
      match l:
        case None{}:
          Con{Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " inherits from itself"}, er.lins(pt, lt, (id + 1 : U32), obs, all)}
        case Some{z}:
          match z:
            case Lz{+ok, ord}:
              when(List<&2, Er>, ok, u => er.lins(pt, lt, (id + 1 : U32), obs, all),
                u => List.append(&2, Er, c3.er.k(obs, id, p, lin.seqs(p, all)), er.lins(pt, lt, (id + 1 : U32), obs, all)))
    case _ _:
      Nil{}

# Definitions
# -----------
#
# An object's definitions: its linearization's members applied from its
# base to itself, each name with the objects that gave it, the latest
# first (an upd's prior is the next), the line of the latest, and what it
# is: a definition (0), a law (1), a law's proof (2), a lemma (3).

type En is Data:
  En{name: List<&2, U32>, chain: List<&2, U32>, +no: U32, +what: U32}

# a member's error: its object and line, its kind (0 an introduction of a
# name another object has, 1 a name its object gives twice, 2 an update of
# nothing, 3 an update of a law or of another kind of member), its name
# and upd or def, the object and line it met, what the member is and what
# it met
type Fe is Data:
  Fe{+q: U32, +mno: U32, +kind: U32, name: List<&2, U32>, +upd: Bool, +origin: U32, +ono: U32, +what: U32, +was: U32}

type Fd is Data:
  Fd{map: List<&2, En>, fes: List<&2, Fe>}

def en.find(es: List<&2, En>, +n: List<&2, U32>) -> Maybe<&2, En>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      match e:
        case En{+name, chain, +no, +what}:
          when(Maybe<&2, En>, same(name, n), u => Some{e}, u => en.find(t, n))

def en.set(es: List<&2, En>, +e: En, +n: List<&2, U32>) -> List<&2, En>:
  match es:
    case Nil{}:
      [e]
    case Con{+x, +t}:
      match x:
        case En{+name, chain, +no, +what}:
          when(List<&2, En>, same(name, n), u => Con{e, t}, u => Con{x, en.set(t, e, n)})

def en.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+h, t}:
      h

# an introduction met an entry: twice in one object, or from another
def fd.def.at(+q: U32, +no: U32, +name: List<&2, U32>, +what: U32, e: En, map: List<&2, En>, fes: List<&2, Fe>) -> Fd:
  match e:
    case En{n, +chain, +eno, +was}:
      Fd{en.set(map, En{name, [q], no, what}, name),
        Con{Fe{q, no, when(U32, U32.is_eq(en.head(chain), q), u => 1, u => 0), name, False{}, en.head(chain), eno, what, was}, fes}}

# whether an update may replace what it meets: never a law, and a
# definition only by a definition, a lemma by a lemma
def upd.fits(+what: U32, +was: U32) -> Bool:
  Bool.not(U32.is_eq(was, 1)) && Bool.not(Bool.xor(U32.is_eq(what, 0), U32.is_eq(was, 0)))

def fd.upd.at(+q: U32, +no: U32, +name: List<&2, U32>, +what: U32, e: En, +map: List<&2, En>, +fes: List<&2, Fe>) -> Fd:
  match e:
    case En{n, +chain, +eno, +was}:
      when(Fd, Bool.not(upd.fits(what, was)), u => Fd{map, Con{Fe{q, no, 3, name, True{}, en.head(chain), eno, what, was}, fes}},
        u => when(Fd, U32.is_eq(en.head(chain), q),
          v => Fd{en.set(map, En{name, chain, no, was}, name), Con{Fe{q, no, 1, name, True{}, q, eno, what, was}, fes}},
          v => Fd{en.set(map, En{name, Con{q, chain}, no, was}, name), fes}))

def fd.def(+q: U32, +upd: Bool, +name: List<&2, U32>, +no: U32, +what: U32, d: Fd) -> Fd:
  match d:
    case Fd{+map, +fes}:
      on.maybe(En, Fd, en.find(map, name),
        u => when(Fd, upd,
          v => Fd{en.set(map, En{name, [q], no, what}, name), Con{Fe{q, no, 2, name, True{}, q, no, what, what}, fes}},
          v => Fd{en.set(map, En{name, [q], no, what}, name), fes}),
        +e => when(Fd, upd, v => fd.upd.at(q, no, name, what, e, map, fes), v => fd.def.at(q, no, name, what, e, map, fes)))

def fd.mems(ns: List<&2, Node>, +q: U32, d: Fd) -> Fd:
  match ns:
    case Nil{}:
      d
    case Con{nd, t}:
      match nd:
        case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
          fd.mems(t, q, fd.def(q, upd, name, no, what, d))
        case _:
          fd.mems(t, q, d)

def fd.obs(qs: List<&2, U32>, +obs: List<&2, Ob>, d: Fd) -> Fd:
  match qs:
    case Nil{}:
      d
    case Con{+q, t}:
      fd.obs(t, obs, fd.mems(ob.mems(ob.at(obs, q)), q, d))

# an object's definitions and its members' errors, its linearization sound
def fold(+obs: List<&2, Ob>, l: Maybe<&2, Lz>) -> Maybe<&2, Fd>:
  match l:
    case None{}:
      None{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          when(Maybe<&2, Fd>, ok, u => Some{fd.obs(List.reverse(&2, U32, ord), obs, Fd{Nil{}, Nil{}})}, u => None{})

# each object's definitions, a mixin's none: it means something only in
# the nested objects made of it
def folds.go(ls: List<&2, Maybe<&2, Lz>>, +obs: List<&2, Ob>, +bad: List<&2, U32>, +id: U32) -> List<&2, Maybe<&2, Fd>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      Con{when(Maybe<&2, Fd>, Bool.not(is.object(ob.kind(ob.at(obs, id)))) || has(bad, id), u => None{}, u => fold(obs, l)), folds.go(t, obs, bad, (id + 1 : U32))}

# each object's definitions; none for a nested object whose contributors
# are wrong already (bad), its error enough
def folds(ls: List<&2, Maybe<&2, Lz>>, +obs: List<&2, Ob>, +bad: List<&2, U32>) -> List<&2, Maybe<&2, Fd>>:
  folds.go(ls, obs, bad, 0)

def fd.or(m: Maybe<&2, Maybe<&2, Fd>>) -> Maybe<&2, Fd>:
  match m:
    case None{}:
      None{}
    case Some{f}:
      f

def fd.at(+fds: List<&2, Maybe<&2, Fd>>, +id: U32) -> Maybe<&2, Fd>:
  fd.or(List.get(&2, Maybe<&2, Fd>, fds, U32.to_nat(id)))

def fe.lines(fes: List<&2, Fe>) -> List<&2, U32>:
  match fes:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Fe{+q, +mno, +kind, name, +upd, +origin, +ono, +what, +was}:
          Con{mno, fe.lines(t)}

def fd.lines(m: Maybe<&2, Fd>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{map, fes}:
          fe.lines(fes)

# the members' error lines of an object's parents: their own reports
def seen(ps: List<&2, U32>, +fds: List<&2, Maybe<&2, Fd>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      List.append(&2, U32, fd.lines(fd.at(fds, p)), seen(t, fds))

def kw(+upd: Bool) -> String:
  match upd:
    case True{}:
      "upd "
    case False{}:
      "def "

# a proof's name, its law's, or a witness's, its declaration's: the `#`
# or `!` that keeps them apart dropped
def name.plain(+n: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, ends(n, [35]) || ends(n, [33]), u => List.take(&2, U32, n, Nat.sub(List.length(&2, U32, n), 1n)), u => n)

# the name emitted: a proof's its law's, a witness's `f.as_declared`
def name.out(+n: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, ends(n, [33]), u => List.append(&2, U32, name.plain(n), codes(".as_declared")), u => name.plain(n))

# a member as messages name it, by what it is: a proof, named `#` after
# its law's name inside Blend, by its law
def mem.say(+name: List<&2, U32>, +what: U32) -> String:
  match what:
    case 1:
      "law " ++ text(name)
    case 2:
      "a proof of " ++ text(name.plain(name))
    case 3:
      "proof " ++ text(name)
    case 4:
      "a declaration of " ++ text(name.plain(name))
    case _:
      text(name)

def mem.no(+name: List<&2, U32>, +what: U32) -> String:
  match what:
    case 1:
      "no law " ++ text(name)
    case 2:
      "no proof of " ++ text(name.plain(name))
    case 3:
      "no proof " ++ text(name)
    case 4:
      "no declaration of " ++ text(name.plain(name))
    case _:
      "no " ++ text(name)

# the keyword that introduces it
def intro.kw(+what: U32) -> String:
  match what:
    case 0:
      "def"
    case 1:
      "law"
    case 4:
      "declare"
    case _:
      "proof"

def upd.kw(+what: U32) -> String:
  match what:
    case 0:
      "upd"
    case _:
      "upd proof"

# the member's line as written, `upd proof right_id`
def mem.kw(+upd: Bool, +name: List<&2, U32>, +what: U32) -> String:
  when(String, upd, u => upd.kw(what) ++ " ", u => intro.kw(what) ++ " ") ++ text(name.plain(name))

# an introduction meeting a name its object has: an update the cure,
# unless a law is either
def fe.met(+obs: List<&2, Ob>, +q: U32, +mno: U32, +name: List<&2, U32>, +upd: Bool, +origin: U32, +what: U32, +was: U32) -> Er:
  when(Er, U32.is_eq(what, 4), v => Er{mno, mem.kw(upd, name, what) ++ ": " ++ ob.name(obs, q) ++ " has " ++ mem.say(name, was) ++ " already, from " ++
      ob.name(obs, origin) ++ ": a declaration is fixed where it is first made, the families varying by their types"},
   v => when(Er, U32.is_eq(what, 1) || U32.is_eq(was, 1),
    u => Er{mno, mem.kw(upd, name, what) ++ ": " ++ ob.name(obs, q) ++ " has " ++ mem.say(name, was) ++ " already, from " ++
      ob.name(obs, origin) ++ ": a law is stated once, so name this " ++ when(String, U32.is_eq(what, 1), v => "law", v => "member") ++ " anew"},
    u => Er{mno, mem.kw(upd, name, what) ++ ": " ++ ob.name(obs, q) ++ " has " ++ mem.say(name, was) ++ " already, from " ++
      ob.name(obs, origin) ++ " (update it with " ++ upd.kw(what) ++ ")"}))

def fe.msg(+obs: List<&2, Ob>, +id: U32, f: Fe) -> Er:
  match f:
    case Fe{+q, +mno, +kind, +name, +upd, +origin, +ono, +what, +was}:
      match kind:
        case 1:
          Er{mno, mem.say(name, what) ++ " is given twice in " ++ ob.name(obs, q) ++ ", at lines " ++ U32.show(ono) ++ " and " ++ U32.show(mno)}
        case 2:
          when(Er, is.root(obs, q),
            u => Er{mno, mem.kw(upd, name, what) ++ ": the module is no object, so it has nothing to update (introduce it with " ++ intro.kw(what) ++ ")"},
            u => Er{mno, mem.kw(upd, name, what) ++ ": " ++ ob.name(obs, q) ++ " has " ++ mem.no(name, what) ++ " to update (introduce it with " ++ intro.kw(what) ++ ")"})
        case 3:
          when(Er, U32.is_eq(was, 1),
            u => Er{mno, mem.kw(upd, name, what) ++ ": " ++ text(name) ++ " is a law, from " ++ ob.name(obs, origin) ++
              ", stated once and never updated (state a new law, or update its proof with upd proof)"},
            u => Er{mno, mem.kw(upd, name, what) ++ ": " ++ ob.name(obs, q) ++ " has " ++ mem.say(name, was) ++ " from " ++ ob.name(obs, origin) ++
              ", which " ++ upd.kw(what) ++ " cannot update (update it with " ++ upd.kw(was) ++ ")"})
        case _:
          when(Er, U32.is_eq(q, id), u => fe.met(obs, q, mno, name, upd, origin, what, was),
            u => Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " has " ++ text(name) ++ " from both " ++ ob.say(obs, origin) ++
              " and " ++ ob.say(obs, q) ++ ", each introducing it with " ++ intro.kw(was)})

def er.fes(fes: List<&2, Fe>, +skip: List<&2, U32>, +obs: List<&2, Ob>, +id: U32) -> List<&2, Er>:
  match fes:
    case Nil{}:
      Nil{}
    case Con{+f, +t}:
      match f:
        case Fe{+q, +mno, +kind, +name, +upd, +origin, +ono, +what, +was}:
          when(List<&2, Er>, has(skip, mno), u => er.fes(t, skip, obs, id),
            u => Con{fe.msg(obs, id, Fe{q, mno, kind, name, upd, origin, ono, what, was}), er.fes(t, skip, obs, id)})

# Declarations
# ------------

# a declared name, the object declaring it, and the line
type Dn is Data:
  Dn{name: List<&2, U32>, +q: U32, +no: U32}

def decl.tag(ns: List<&2, List<&2, U32>>, +q: U32, +no: U32) -> List<&2, Dn>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{Dn{n, q, no}, decl.tag(t, q, no)}

def decl.names(ns: List<&2, Node>, +q: U32) -> List<&2, Dn>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NDecl{names, +no}:
          List.append(&2, Dn, decl.tag(names, q, no), decl.names(t, q))
        case _:
          decl.names(t, q)

def decl.obs(qs: List<&2, U32>, +obs: List<&2, Ob>) -> List<&2, Dn>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      List.append(&2, Dn, decl.names(ob.mems(ob.at(obs, q)), q), decl.obs(t, obs))

def decl.missing(+obs: List<&2, Ob>, +id: U32, +n: List<&2, U32>, +q: U32, +no: U32) -> Er:
  Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " defines no " ++ text(n) ++ ", which " ++ ob.name(obs, q) ++
    " declares (or mark " ++ ob.name(obs, id) ++ " abstract)"}

def decl.check.k(+obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>, +n: List<&2, U32>, +q: U32, +no: U32) -> List<&2, Er>:
  when(List<&2, Er>, names.has(done, n) || Maybe.is_some(&2, En, en.find(map, n)), u => Nil{},
    u => [decl.missing(obs, id, n, q, no)])

def decl.check(+obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>, d: Dn) -> List<&2, Er>:
  match d:
    case Dn{+n, +q, +no}:
      decl.check.k(obs, id, map, done, n, q, no)

def decl.pair.name(d: Dn) -> List<&2, U32>:
  match d:
    case Dn{n, +q, +no}:
      n

def decl.go(ds: List<&2, Dn>, +obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>) -> List<&2, Er>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, t}:
      List.append(&2, Er, decl.check(obs, id, map, done, d), decl.go(t, obs, id, map, Con{decl.pair.name(d), done}))

# a concrete object's declared names it gives no definition, each once
def er.decls(+obs: List<&2, Ob>, +id: U32, +ord: List<&2, U32>, +map: List<&2, En>) -> List<&2, Er>:
  when(List<&2, Er>, ob.abs(ob.at(obs, id)) || is.root(obs, id) || Bool.not(is.object(ob.kind(ob.at(obs, id)))), u => Nil{}, u => decl.go(decl.obs(List.reverse(&2, U32, ord), obs), obs, id, map, Nil{}))

def er.def.k(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, +fds: List<&2, Maybe<&2, Fd>>, +ord: List<&2, U32>, m: Maybe<&2, Fd>) -> List<&2, Er>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{+map, fes}:
          List.append(&2, Er, er.fes(fes, seen(ps, fds), obs, id), er.decls(obs, id, ord, map))

# each object's errors of definition and declaration
def er.defs(ps: List<&2, List<&2, U32>>, fs: List<&2, Maybe<&2, Fd>>, ls: List<&2, Maybe<&2, Lz>>, +id: U32, +obs: List<&2, Ob>, +fds: List<&2, Maybe<&2, Fd>>) -> List<&2, Er>:
  match ps fs ls:
    case Con{+p, pt} Con{f, ft} Con{l, lt}:
      List.append(&2, Er, er.def.k(obs, id, p, fds, lz.ord(l), f), er.defs(pt, ft, lt, (id + 1 : U32), obs, fds))
    case _ _ _:
      Nil{}

# The objects, printed
# --------------------

def show.ids(+obs: List<&2, Ob>, xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      match t:
        case Nil{}:
          ob.name(obs, x)
        case Con{h, r}:
          ob.name(obs, x) ++ ", " ++ show.ids(obs, Con{h, r})

def show.chain(+obs: List<&2, Ob>, xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      match t:
        case Nil{}:
          ob.name(obs, x)
        case Con{h, r}:
          ob.name(obs, x) ++ " < " ++ show.chain(obs, Con{h, r})

def show.ens(+obs: List<&2, Ob>, es: List<&2, En>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      match e:
        case En{name, chain, +no, +what}:
          "  " ++ text(name) ++ ": " ++ show.chain(obs, chain) ++ "\n" ++ show.ens(obs, t)

def show.fd(+obs: List<&2, Ob>, m: Maybe<&2, Fd>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      match d:
        case Fd{map, fes}:
          show.ens(obs, map)

def show.en.names(es: List<&2, En>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      match e:
        case En{name, chain, +no, +what}:
          "  " ++ text(name) ++ "\n" ++ show.en.names(t)

# the module's definitions, Bend's, by name alone
def show.fd.names(m: Maybe<&2, Fd>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      match d:
        case Fd{map, fes}:
          show.en.names(map)

def show.abs.of(+a: Bool) -> String:
  match a:
    case True{}:
      "abstract "
    case False{}:
      ""

def show.kind.of(+k: U32, +bound: Bool) -> String:
  match k:
    case 1:
      when(String, bound, u => "mixin bound ", u => "mixin ")
    case 2:
      when(String, bound, u => "extension bound ", u => "extension ")
    case _:
      ""

def show.ob(+obs: List<&2, Ob>, o: Ob, l: Maybe<&2, Lz>, +f: Maybe<&2, Fd>) -> String:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
      when(String, U32.is_eq(id, host), u => "module\n" ++ show.fd.names(f),
        u => show.kind.of(kind, Bool.not(U32.is_eq(tpl, id))) ++ show.abs.of(abs) ++ ob.say(obs, id) ++ ": " ++ show.ids(obs, lz.ord(l)) ++ "\n" ++ show.fd(obs, f))

# each object, its linearization, and each definition it has with the
# objects that gave it, the final first
def show.obs(os: List<&2, Ob>, ls: List<&2, Maybe<&2, Lz>>, fs: List<&2, Maybe<&2, Fd>>, +obs: List<&2, Ob>) -> String:
  match os ls fs:
    case Con{o, ot} Con{l, lt} Con{f, ft}:
      show.ob(obs, o, l, f) ++ show.obs(ot, lt, ft, obs)
    case _ _ _:
      ""

def show.ers.more(es: List<&2, Er>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      "\n"

# Locations
#
# Each module's lines are numbered from k * 1000000, k its place among
# the modules read (the root 0th), so that a line's number names its file
# too: errors and markers decode it.

def loc.file(+files: List<&2, List<&2, U32>>, +no: U32) -> List<&2, U32>:
  on.maybe(List<&2, U32>, List<&2, U32>, List.get(&2, List<&2, U32>, files, U32.to_nat(loc.mod(no))), u => codes("blend"), x => x)

def er.at(+no: U32) -> String:
  when(String, U32.is_eq(loc.line(no), 0), u => "", u => ":" ++ U32.show(loc.line(no)))

# errors, each `FILE:LINE: message`, a line 0 left out
def show.ers(+files: List<&2, List<&2, U32>>, es: List<&2, Er>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, +t}:
      match e:
        case Er{+no, msg}:
          text(loc.file(files, no)) ++ er.at(no) ++ ": " ++ msg ++ show.ers.more(t) ++ show.ers(files, t)

# References
# ==========
#
# Each concrete object's definitions, its own copies, their bodies'
# names bound (`blend-resolve`): a bare name to the final definition of
# the innermost object that has it, the concrete object itself first,
# then the hosts of the object that wrote the body, the module's
# definitions last, Bend's, their names kept; a dotted name to an object's
# definition (`Outer.Inner.path`), the longest object path first; `_name`
# to the definition the writer's replaced, `^name` to its host's, `~name`
# as a bare name, the mark kept. A body's locals are its parameters and
# binders; a local named as an object's definition is an error
# (`shadowing-is-an-error`), so any other name a definition has is a
# reference. The rest is Bend's. The module's definitions are Bend's
# (`blend-module-is-bend`): their names are bound only to order them, and
# to find the objects' definitions they use.

# the module, its objects, their linearizations and definitions
type Cx is Data:
  Cx{obs: List<&2, Ob>, ls: List<&2, Maybe<&2, Lz>>, fs: List<&2, Maybe<&2, Fd>>, als: List<&2, Al>, paths: List<&2, List<&2, U32>>,
    pss: List<&2, List<&2, U32>>}

def cx.obs(c: Cx) -> List<&2, Ob>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      obs

def cx.paths(c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      paths

def cx.als(c: Cx) -> List<&2, Al>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      als

def fd.map(m: Maybe<&2, Fd>) -> List<&2, En>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{map, fes}:
          map

def cx.map(c: Cx, +id: U32) -> List<&2, En>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      fd.map(fd.at(fs, id))

def cx.ord(c: Cx, +id: U32) -> List<&2, U32>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      lz.ord(lz.at(ls, id))

def has.def(+map: List<&2, En>, +n: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, En, en.find(map, n))

# an object's hosts, innermost first, the module last: `^name` names the
# host's scope, the module's at the top, though the module is no object
# (`blend-module-is-bend`); the module has none
def hosts.go(n: Nat, +obs: List<&2, Ob>, +id: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n++k:
      when(List<&2, U32>, is.root(obs, id), u => Nil{},
        u => Con{ob.host(ob.at(obs, id)), hosts.go(k, obs, ob.host(ob.at(obs, id)))})

def hosts(+obs: List<&2, Ob>, +id: U32) -> List<&2, U32>:
  hosts.go(1n+List.length(&2, Ob, obs), obs, id)

def cx.pss(c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{obs, ls, fs, als, paths, pss}:
      pss

def ids.or(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def ids.at(+xss: List<&2, List<&2, U32>>, +i: U32) -> List<&2, U32>:
  ids.or(List.get(&2, List<&2, U32>, xss, U32.to_nat(i)))

# A body's locals
# ---------------

def tok.sym(t: Tok, +c: U32) -> Bool:
  match t:
    case TSym{+x}:
      U32.is_eq(x, c)
    case _:
      False{}

# whether ts begins with the symbol c
def tok.sym.head(ts: List<&2, Tok>, +c: U32) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      tok.sym(t, c)

def tok.solid(ts: List<&2, Tok>) -> List<&2, Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case TSp{x}:
          tok.solid(r)
        case TCom{x}:
          tok.solid(r)
        case _:
          Con{t, tok.solid(r)}

def tok.brace(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      tok.sym(t, 123)

def tok.arrow(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Con{a, r}:
      match r:
        case Con{b, r2}:
          tok.sym(a, 61) && tok.sym(b, 62)
        case Nil{}:
          False{}
    case Nil{}:
      False{}

def is.wild(+x: List<&2, U32>) -> Bool:
  same(x, codes("_"))

# a pattern's binders: its names, but constructors (a name before `{`)
# and `_`; up to the pattern's `:`
def pat.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.brace(r) || is.wild(x), u => pat.names(r), u => Con{x, pat.names(r)})
        case TSym{+c}:
          match c:
            case 58:
              Nil{}
            case _:
              pat.names(r)
        case _:
          pat.names(r)

# a let's binders: names, brackets, commas and marks, then a lone `=`
def let.names(+ts: List<&2, Tok>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          let.names(r, when(List<&2, List<&2, U32>>, tok.brace(r) || is.wild(x), u => acc, u => Con{x, acc}))
        case TSym{+c}:
          match c:
            case 61:
              when(List<&2, List<&2, U32>>, tok.arrow(Con{TSym{c}, r}) || tok.sym.head(r, 61), u => Nil{}, u => acc)
            case 40:
              let.names(r, acc)
            case 41:
              let.names(r, acc)
            case 44:
              let.names(r, acc)
            case 43:
              let.names(r, acc)
            case 45:
              let.names(r, acc)
            case 123:
              let.names(r, acc)
            case 125:
              let.names(r, acc)
            case _:
              Nil{}
        case _:
          Nil{}

# a lambda's binders: each name before `=>`
def lam.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.arrow(r), u => Con{x, lam.names(r)}, u => lam.names(r))
        case _:
          lam.names(r)

# a bind's or an annotated let's binder: a line's first name before `:`
def bind.name(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TSym{+c}:
          match c:
            case 43:
              bind.name(r)
            case 45:
              bind.name(r)
            case _:
              Nil{}
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.sym.head(r, 58), u => [x], u => Nil{})
        case _:
          Nil{}

def is.case(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      match t:
        case TName{x}:
          same(x, codes("case"))
        case _:
          False{}

def line.names.k(+pat: Bool, +ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match pat:
    case True{}:
      List.append(&2, List<&2, U32>, pat.names(List.tail(&2, Tok, ts)), lam.names(ts))
    case False{}:
      List.append(&2, List<&2, U32>, let.names(ts, Nil{}), List.append(&2, List<&2, U32>, bind.name(ts), lam.names(ts)))

# a law's `for +x: T`: x
def for.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      match t:
        case TName{+x}:
          when(List<&2, List<&2, U32>>, same(x, codes("for")), u => bind.name(r), u => Nil{})
        case _:
          Nil{}

def line.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  List.append(&2, List<&2, U32>, for.names(tok.solid(ts)), line.names.k(is.case(tok.solid(ts)), tok.solid(ts)))

# A name bound
# ------------

# where a name points: a final definition (obj's), or a prior (the one
# origin gave, in obj's copy)
type Rf is Data:
  Rf{+obj: U32, name: List<&2, U32>, +prior: Bool, +origin: U32}

# a body's token, a reference resolved or as written; or a name of Bend's
# a body copied from another module wrote through one of that module's
# imports, or a datatype's of that module: its file, and the name after
# its alias (Namespaces, below)
type Rt is Data:
  RT{t: Tok}
  RR{+mark: U32, ref: Rf}
  RX{+mark: U32, path: List<&2, U32>, rest: List<&2, U32>}

type Rl is Data:
  Rl{+no: U32, +ind: U32, ts: List<&2, Rt>}

# a definition in a concrete object's copy: its name, the object whose
# member it is, whether it is a prior
type In is Data:
  In{name: List<&2, U32>, +q: U32, +prior: Bool}

# a token resolved, the errors it raised, the priors it reached
type Rr is Data:
  Rr{rt: Rt, ers: List<&2, Er>, ins: List<&2, In>}

# a name token's text
def tok.txt(t: Tok) -> List<&2, U32>:
  match t:
    case TName{x}:
      x
    case _:
      Nil{}

def rr.tok(t: Tok) -> Rr:
  Rr{RT{t}, Nil{}, Nil{}}

def rr.er(t: Tok, +no: U32, msg: String) -> Rr:
  Rr{RT{t}, [Er{no, msg}], Nil{}}

def carets(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+h, t}:
      match h:
        case 94:
          1n+carets(t)
        case _:
          0n

def nth(+xs: List<&2, U32>, n: Nat) -> Maybe<&2, U32>:
  List.get(&2, U32, xs, n)

# a reference to obj's final n, an error where obj is abstract
def rr.final(+cx: Cx, +obj: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  when(Rr, ob.abs(ob.at(cx.obs(cx), obj)),
    u => rr.er(t, no, text(tok.txt(t)) ++ " names a definition of " ++ ob.name(cx.obs(cx), obj) ++ ", which is abstract and emits nothing"),
    u => Rr{RR{mark, Rf{obj, n, False{}, obj}}, Nil{}, Nil{}})

# a bare name: the concrete object's, then each host's, innermost first
def look(+cx: Cx, hs: List<&2, U32>, +n: List<&2, U32>) -> Maybe<&2, U32>:
  match hs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      when(Maybe<&2, U32>, has.def(cx.map(cx, h), n), u => Some{h}, u => look(cx, t, n))

# a dotted name as an object's path and one of its definitions, the
# longest path first; k, the path's length tried
def look.obj(k: Nat, +cx: Cx, +q: U32, +ps: List<&2, List<&2, U32>>) -> Maybe<&2, Rf>:
  match k:
    case 0n:
      None{}
    case 1n++j:
      on.maybe(U32, Maybe<&2, Rf>, resolve(List.length(&2, Ob, cx.obs(cx)), cx.als(cx), cx.obs(cx), q, List.take(&2, List<&2, U32>, ps, k)),
        u => look.obj(j, cx, q, ps),
        +x => when(Maybe<&2, Rf>, has.def(cx.map(cx, x), dots(List.drop(&2, List<&2, U32>, ps, k))),
          v => Some{Rf{x, dots(List.drop(&2, List<&2, U32>, ps, k)), False{}, x}},
          v => look.obj(j, cx, q, ps)))

def rr.rf(+cx: Cx, +mark: U32, +t: Tok, +no: U32, f: Rf) -> Rr:
  match f:
    case Rf{+obj, +name, +prior, +origin}:
      rr.final(cx, obj, mark, name, t, no)

# Namespaces
#
# A module's names are its own: a file's definitions, datatypes and
# constructors by their names, another's through an alias the file
# imports, an alias local to the file that imports it, as Bend's are
# (tried 2026-11-04). So a body copied from another module keeps its
# meaning: its module's aliases, and its module's datatypes and
# constructors, named in the root's emission through the root's own
# alias for that file, else one Blend reserves, `Blend_1` and on, which
# no name the user writes may begin (the maintainer, 2026-11-04: no
# surprises, the root's namespace no larger for what it inherits).

def lines.names(ls: List<&2, Ln>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, +txt}:
          Con{param.first(until(trim(txt), 123)), lines.names(t)}

# a datatype's name, and its constructors', each the name its line opens
def bend.names(ls: List<&2, Ln>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, +txt}:
          Con{param.first(until(param.first(until(drop(5n, txt), 60)), 32)), lines.names(t)}

def tree.types(ns: List<&2, Node>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NBend{lines, +no}:
          List.append(&2, List<&2, U32>, bend.names(lines), tree.types(t))
        case _:
          tree.types(t)

def root.find(obs: List<&2, Ob>, +m: U32) -> U32:
  match obs:
    case Nil{}:
      0
    case Con{o, t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          when(U32, U32.is_eq(id, host) && U32.is_eq(loc.mod(no), m), u => id, u => root.find(t, m))

def ims.of(ns: List<&2, Node>) -> List<&2, Im>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, +t}:
      match nd:
        case NImport{+txt, +no}:
          on.maybe(Im, List<&2, Im>, im.of(txt, no), u => ims.of(t), x => Con{x, ims.of(t)})
        case _:
          ims.of(t)

def path.at(+ps: List<&2, List<&2, U32>>, +k: U32) -> List<&2, U32>:
  on.maybe(List<&2, U32>, List<&2, U32>, List.get(&2, List<&2, U32>, ps, U32.to_nat(k)), u => Nil{}, x => x)

def mod.tree(+cx: Cx, +m: U32) -> List<&2, Node>:
  ob.mems(ob.at(cx.obs(cx), root.find(cx.obs(cx), m)))

# an import carried: its alias, its file as a path from where the root
# was read, and the line that gives it
type Ci is Data:
  Ci{alias: List<&2, U32>, path: List<&2, U32>, +no: U32}

def bendify(+p: List<&2, U32>, +blend: Bool) -> List<&2, U32>:
  when(List<&2, U32>, blend, u => List.append(&2, U32, List.take(&2, U32, p, Nat.sub(List.length(&2, U32, p), 5n)), codes("bend")), u => p)

# whether the last part kept is a `..` itself, which another cannot take
def path.up(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      same(x, codes(".."))

def path.norm(ps: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, acc)
    case Con{+p, +t}:
      when(List<&2, List<&2, U32>>, same(p, codes(".")) || blank(p), u => path.norm(t, acc),
        u => when(List<&2, List<&2, U32>>, same(p, codes("..")) && Bool.not(blank.parts(acc)) && Bool.not(path.up(acc)),
          v => path.norm(t, List.tail(&2, List<&2, U32>, acc)), v => path.norm(t, Con{p, acc})))

def slashes(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match t:
        case Nil{}:
          p
        case Con{h, r}:
          List.append(&2, U32, p, Con{47, slashes(Con{h, r})})

# a file's directory's parts
def path.dir(+path: List<&2, U32>) -> List<&2, List<&2, U32>>:
  List.reverse(&2, List<&2, U32>, List.tail(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, split.slash(path, Nil{}, Nil{}))))

def path.from.k(+path: List<&2, U32>, +rel: List<&2, U32>) -> List<&2, U32>:
  slashes(path.norm(List.append(&2, List<&2, U32>, path.dir(path), split.slash(rel, Nil{}, Nil{})), Nil{}))

# rel, written in a file at path, as a path from where the root was read;
# a root named by its absolute path keeps its `/`
def path.from(+path: List<&2, U32>, +rel: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(path, [47]), u => Con{47, path.from.k(path, rel)}, u => path.from.k(path, rel))

# a path made plain, `.` and `..` resolved, as an import's is
def path.plain(+p: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(p, [47]), u => Con{47, slashes(path.norm(split.slash(p, Nil{}, Nil{}), Nil{}))},
    u => slashes(path.norm(split.slash(p, Nil{}, Nil{}), Nil{})))

def cis.of(xs: List<&2, Im>, +mpath: List<&2, U32>) -> List<&2, Ci>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      match i:
        case Im{+p, +alias, +blend, +no}:
          Con{Ci{alias, bendify(path.from(mpath, p), blend), no}, cis.of(t, mpath)}

# module m's imports, by alias and file
def mod.cis(+cx: Cx, +m: U32) -> List<&2, Ci>:
  cis.of(ims.of(mod.tree(cx, m)), path.at(cx.paths(cx), m))

def ci.find(cs: List<&2, Ci>, +a: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Ci{+alias, +path, +no}:
          when(Maybe<&2, List<&2, U32>>, same(alias, a), u => Some{path}, u => ci.find(t, a))

# a Bend name another module's body wrote: through one of that module's
# imports, or one of its datatypes' names, else Bend's own (Base's)
def rr.foreign(+cx: Cx, +m: U32, +mark: U32, +n: List<&2, U32>, +t: Tok) -> Rr:
  when(Rr, Bool.not(blank.parts(List.tail(&2, List<&2, U32>, parts(n)))),
    u => on.maybe(List<&2, U32>, Rr, ci.find(mod.cis(cx, m), List.head.or(parts(n))), v => rr.tok(t),
      +p => Rr{RX{mark, p, drop(1n+List.length(&2, U32, List.head.or(parts(n))), n)}, Nil{}, Nil{}}),
    u => when(Rr, names.has(tree.types(mod.tree(cx, m)), n),
      v => Rr{RX{mark, bendify(path.at(cx.paths(cx), m), True{}), n}, Nil{}, Nil{}},
      v => rr.tok(t)))

# a name no definition of Blend's has: Bend's, in the root's own bodies,
# but for the prefix Blend reserves; another module's names in a body
# copied from it
def rr.bend(+cx: Cx, +q: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  when(Rr, U32.is_eq(loc.mod(ob.no(ob.at(cx.obs(cx), q))), 0),
    u => when(Rr, starts(n, codes("Blend_")), v => rr.er(t, no, text(n) ++ ": names beginning Blend_ are Blend's own"), v => rr.tok(t)),
    u => rr.foreign(cx, loc.mod(ob.no(ob.at(cx.obs(cx), q))), mark, n, t))

def rr.dotted(+cx: Cx, +q: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  on.maybe(Rf, Rr, look.obj(List.length(&2, List<&2, U32>, List.tail(&2, List<&2, U32>, parts(n))), cx, q, parts(n)),
    u => rr.bend(cx, q, mark, n, t, no),
    f => rr.rf(cx, mark, t, no, f))

# a name with no mark, or after `~`: a local, as written (local), else an
# object's definition, a definition of the module (Bend's, its text
# kept), or Bend's
def rr.plain.k(+local: Bool, +cx: Cx, +o: U32, +q: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  match local:
    case True{}:
      rr.tok(t)
    case False{}:
      on.maybe(U32, Rr, look(cx, Con{o, hosts(cx.obs(cx), q)}, n),
        v => rr.dotted(cx, q, mark, n, t, no),
        +h => rr.final(cx, h, mark, n, t, no))

def rr.plain(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  rr.plain.k(names.has(locals, n), cx, o, q, mark, n, t, no)

# the first of the definers, latest first, that comes after q in o's
# linearization
def prior.find(cs: List<&2, U32>, +after: List<&2, U32>) -> Maybe<&2, U32>:
  match cs:
    case Nil{}:
      None{}
    case Con{+c, t}:
      when(Maybe<&2, U32>, has(after, c), u => Some{c}, u => prior.find(t, after))

def after(xs: List<&2, U32>, +q: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, U32.is_eq(x, q), u => t, u => after(t, q))

def en.chain(m: Maybe<&2, En>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{e}:
      match e:
        case En{name, chain, +no, +what}:
          chain

def rr.prior.of(+cx: Cx, +o: U32, +q: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  on.maybe(U32, Rr, prior.find(en.chain(en.find(cx.map(cx, o), n)), after(cx.ord(cx, o), q)),
    u => rr.er(t, no, "_" ++ text(name.plain(n)) ++ ": " ++ ob.name(cx.obs(cx), o) ++ " has no " ++
      when(String, ends(n, [35]), v => "proof of ", v => "definition of ") ++ text(name.plain(n)) ++ " before " ++ ob.name(cx.obs(cx), q) ++ "'s"),
    +c => Rr{RR{0, Rf{o, n, True{}, c}}, Nil{}, [In{n, c, True{}}]})

# `_n`: the definition of n that q's replaced in o's copy; a law has no
# prior, so `_n` of a law n is its proof's, `n#`
def rr.prior(+cx: Cx, +o: U32, +q: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  when(Rr, has.def(cx.map(cx, o), List.append(&2, U32, n, [35])), u => rr.prior.of(cx, o, q, List.append(&2, U32, n, [35]), t, no),
    u => rr.prior.of(cx, o, q, n, t, no))

# `^n`, k carets: the k-th host's final n, the module's definition at
# the top
def rr.host(+cx: Cx, +o: U32, +q: U32, k: Nat, +n: List<&2, U32>, +t: Tok, +whole: List<&2, U32>, +no: U32) -> Rr:
  on.maybe(U32, Rr, List.get(&2, U32, hosts(cx.obs(cx), q), Nat.sub(k, 1n)),
    u => rr.er(t, no, text(whole) ++ " steps out of the module, which has no host"),
    +h => when(Rr, has.def(cx.map(cx, h), n), v => rr.final(cx, h, 0, n, t, no),
      v => rr.er(t, no, text(whole) ++ ": " ++ ob.name(cx.obs(cx), h) ++ " has no " ++ text(n))))

# `_n`: a local, or `_` alone, or in a module's definition, as written
# (local); else a prior
def rr.under(+local: Bool, +cx: Cx, +o: U32, +q: U32, +r: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  match local:
    case True{}:
      rr.tok(t)
    case False{}:
      rr.prior(cx, o, q, r, t, no)

# a name by its first byte's tests: `^` a host's (up), `~` a template's
# argument (tpl), `_` a prior or a local (under), else plain. The bytes
# are tested, not matched, and the tests branched on here, so that a law
# can follow it (blend/LAWS.bend, `locals`): a byte's match leaves a
# proof stuck
def rr.mark.k(+up: Bool, +tpl: Bool, +under: Bool, +cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +h: U32, +r: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  match up tpl under:
    case True{} _ _:
      rr.host(cx, o, q, carets(Con{h, r}), List.drop(&2, U32, Con{h, r}, carets(Con{h, r})), t, Con{h, r}, no)
    case False{} True{} _:
      rr.plain(cx, o, q, locals, 126, r, t, no)
    case False{} False{} True{}:
      rr.under(blank(r) || names.has(locals, Con{h, r}) || is.root(cx.obs(cx), o), cx, o, q, r, t, no)
    case False{} False{} False{}:
      rr.plain(cx, o, q, locals, 0, Con{h, r}, t, no)

def rr.mark(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +h: U32, +r: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  rr.mark.k(U32.is_eq(h, 94), U32.is_eq(h, 126), U32.is_eq(h, 95), cx, o, q, locals, h, r, t, no)

def rr.of(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +t: Tok, +no: U32) -> Rr:
  match t:
    case TName{+x}:
      match x:
        case Nil{}:
          rr.tok(t)
        case Con{+h, +r}:
          rr.mark(cx, o, q, locals, h, r, TName{Con{h, r}}, no)
    case _:
      rr.tok(t)

# A definition's body
# -------------------

type Rb is Data:
  Rb{ls: List<&2, Rl>, ers: List<&2, Er>, ins: List<&2, In>}

def rb.cons(x: Rr, rest: Rb) -> Rb:
  match x rest:
    case Rr{rt, e, i} Rb{ls, es, more}:
      Rb{Con{Rl{0, 0, [rt]}, ls}, List.append(&2, Er, e, es), List.append(&2, In, i, more)}

def rb.toks(ts: List<&2, Tok>, +cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +no: U32) -> Rb:
  match ts:
    case Nil{}:
      Rb{Nil{}, Nil{}, Nil{}}
    case Con{t, r}:
      rb.cons(rr.of(cx, o, q, locals, t, no), rb.toks(r, cx, o, q, locals, no))

# a line's tokens, gathered from rb.toks' one-token lines
def rl.join(ls: List<&2, Rl>) -> List<&2, Rt>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, Rt, ts, rl.join(t))

def rb.line(+no: U32, +ind: U32, b: Rb) -> Rb:
  match b:
    case Rb{ls, es, more}:
      Rb{[Rl{no, ind, rl.join(ls)}], es, more}

def rb.join(a: Rb, b: Rb) -> Rb:
  match a b:
    case Rb{l1, e1, i1} Rb{l2, e2, i2}:
      Rb{List.append(&2, Rl, l1, l2), List.append(&2, Er, e1, e2), List.append(&2, In, i1, i2)}

def rb.lines(bs: List<&2, Bl>, +cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>) -> Rb:
  match bs:
    case Nil{}:
      Rb{Nil{}, Nil{}, Nil{}}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          rb.join(rb.line(no, ind, rb.toks(ts, cx, o, q, locals, no)), rb.lines(t, cx, o, q, locals))

# a body's binders, with the line of each
type Lc is Data:
  Lc{name: List<&2, U32>, +no: U32}

def lc.tag(ns: List<&2, List<&2, U32>>, +no: U32) -> List<&2, Lc>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{Lc{n, no}, lc.tag(t, no)}

def body.binders(bs: List<&2, Bl>) -> List<&2, Lc>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          List.append(&2, Lc, lc.tag(line.names(ts), no), body.binders(t))

def lc.names(ls: List<&2, Lc>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Lc{n, +no}:
          Con{n, lc.names(t)}

def unmark(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      match h:
        case 126:
          t
        case 45:
          t
        case _:
          Con{h, t}

def unmarks(ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{unmark(n), unmarks(t)}

def objs.only(xs: List<&2, U32>, +obs: List<&2, Ob>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, is.root(obs, x), u => objs.only(t, obs), u => Con{x, objs.only(t, obs)})

# whether n names an object's definition a bare name would reach; the
# module's, Bend's, a local may shadow
def visible(+cx: Cx, +o: U32, +q: U32, +n: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, U32, look(cx, objs.only(Con{o, hosts(cx.obs(cx), q)}, cx.obs(cx)), n))

def shadow.params(ps: List<&2, List<&2, U32>>, +cx: Cx, +o: U32, +q: U32, +dn: String, +no: U32) -> List<&2, Er>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      when(List<&2, Er>, visible(cx, o, q, p),
        u => Con{Er{no, "the parameter " ++ text(p) ++ " of " ++ dn ++ " shadows the definition " ++ text(p)}, shadow.params(t, cx, o, q, dn, no)},
        u => shadow.params(t, cx, o, q, dn, no))

def shadow.locals(ls: List<&2, Lc>, +cx: Cx, +o: U32, +q: U32, +dn: String) -> List<&2, Er>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, +t}:
      match l:
        case Lc{+n, +no}:
          when(List<&2, Er>, visible(cx, o, q, n),
            u => Con{Er{no, "the local " ++ text(n) ++ " of " ++ dn ++ " shadows the definition " ++ text(n)}, shadow.locals(t, cx, o, q, dn)},
            u => shadow.locals(t, cx, o, q, dn))

# a resolved definition: what it is, its member as written, its lines
type Rd is Data:
  Rd{inst: In, node: Node, hd: List<&2, Rt>, ls: List<&2, Rl>}

# Copies
# ------

def mem.find(ns: List<&2, Node>, +n: List<&2, U32>) -> Maybe<&2, Node>:
  match ns:
    case Nil{}:
      None{}
    case Con{+nd, t}:
      match nd:
        case NDef{+share, +upd, +name, +rest, +params, +body, +no, +ind, +what}:
          when(Maybe<&2, Node>, same(name, n), u => Some{NDef{share, upd, name, rest, params, body, no, ind, what}}, u => mem.find(t, n))
        case _:
          mem.find(t, n)

# the name a definition is emitted by: `Obj.f`, a prior `Obj.f.Origin`,
# the module's own unprefixed
def path.name(+path: List<&2, List<&2, U32>>, +n: List<&2, U32>) -> List<&2, U32>:
  match path:
    case Nil{}:
      n
    case Con{h, t}:
      List.append(&2, U32, dots(Con{h, t}), Con{46, n})

def rf.text(+obs: List<&2, Ob>, r: Rf) -> List<&2, U32>:
  match r:
    case Rf{+obj, +name, +prior, +origin}:
      when(List<&2, U32>, prior,
        u => List.append(&2, U32, path.name(ob.path(ob.at(obs, obj)), name.out(name)), Con{46, dots(ob.path(ob.at(obs, origin)))}),
        u => path.name(ob.path(ob.at(obs, obj)), name.out(name)))

def in.ref(+o: U32, i: In) -> Rf:
  match i:
    case In{name, +q, +prior}:
      Rf{o, name, prior, q}

def copy.k(i: In, nd: Node, h: Rb, b: Rb, sh: List<&2, Er>) -> Rd & Rb:
  match h b:
    case Rb{hl, he, hi} Rb{ls, es, more}:
      (Rd{i, nd, rl.join(hl), ls}, Rb{Nil{}, List.append(&2, Er, sh, List.append(&2, Er, he, es)), List.append(&2, In, hi, more)})

# a member's copy in o: its body bound, the priors it reaches
def copy.node(+cx: Cx, +o: U32, i: In, +nd: Node) -> Rd & Rb:
  match i:
    case In{+n, +q, +prior}:
      match nd:
        case NDef{+share, +upd, +name, +rest, +params, +body, +no, +ind, +what}:
          copy.k(In{n, q, prior}, nd,
            rb.line(no, 0, rb.toks(toks(rest), cx, o, q, List.append(&2, List<&2, U32>, unmarks(params), lc.names(body.binders(body))), no)),
            rb.lines(body, cx, o, q, List.append(&2, List<&2, U32>, unmarks(params), lc.names(body.binders(body)))),
            when(List<&2, Er>, is.root(cx.obs(cx), o), u => Nil{},
              u => List.append(&2, Er, shadow.params(unmarks(params), cx, o, q, text(rf.text(cx.obs(cx), in.ref(o, In{n, q, prior}))), no),
                shadow.locals(body.binders(body), cx, o, q, text(rf.text(cx.obs(cx), in.ref(o, In{n, q, prior})))))))
        case _:
          (Rd{In{n, q, prior}, nd, Nil{}, Nil{}}, Rb{Nil{}, Nil{}, Nil{}})

def copy.of(+cx: Cx, +o: U32, +i: In) -> Rd & Rb:
  match i:
    case In{+n, +q, +prior}:
      on.maybe(Node, Rd & Rb, mem.find(ob.mems(ob.at(cx.obs(cx), q)), n),
        u => (Rd{i, NBad{Nil{}, 0}, Nil{}, Nil{}}, Rb{Nil{}, Nil{}, Nil{}}),
        nd => copy.node(cx, o, i, nd))

def in.eq(a: In, b: In) -> Bool:
  match a b:
    case In{n, +q, +p} In{m, +r, +s}:
      same(n, m) && U32.is_eq(q, r) && Bool.not(Bool.xor(p, s))

def ins.has(+xs: List<&2, In>, +i: In) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      in.eq(x, i) || ins.has(t, i)

# the copies made so far, their errors
type Cp is Data:
  Cp{rds: List<&2, Rd>, ers: List<&2, Er>, done: List<&2, In>}

def cp.add(rd: Rd, b: Rb, c: Cp) -> Cp:
  match b c:
    case Rb{ls, es, more} Cp{rds, ers, done}:
      Cp{Con{rd, rds}, List.append(&2, Er, ers, es), done}

def rb.ins(b: Rb) -> List<&2, In>:
  match b:
    case Rb{ls, es, more}:
      more

# the worklist of copies: the finals, then each prior reached; fuel, the
# file's definitions
def copies.go(n: Nat, +cx: Cx, +o: U32, todo: List<&2, In>, +c: Cp) -> Cp:
  match n:
    case 0n:
      c
    case 1n++k:
      match todo:
        case Nil{}:
          c
        case Con{+i, +t}:
          match c:
            case Cp{+rds, +ers, +done}:
              when(Cp, ins.has(done, i), u => copies.go(k, cx, o, t, Cp{rds, ers, done}),
                u => on.pair(Rd, Rb, Cp, copy.of(cx, o, i),
                  rd => +b => copies.go(k, cx, o, List.append(&2, In, t, rb.ins(b)), cp.add(rd, b, Cp{rds, ers, Con{i, done}}))))

def ins.finals(es: List<&2, En>) -> List<&2, In>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      match e:
        case En{name, chain, +no, +what}:
          Con{In{name, en.head(chain), False{}}, ins.finals(t)}

# a concrete object's copies: its finals, then each prior they reach
def copies(+cx: Cx, +o: U32) -> Cp:
  copies.go(1n+count(ob.mems(ob.at(cx.obs(cx), 0))), cx, o, ins.finals(cx.map(cx, o)), Cp{Nil{}, Nil{}, Nil{}})

# The copies, printed
# -------------------

def show.rts(+obs: List<&2, Ob>, ts: List<&2, Rt>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case RR{+mark, ref}:
          Con{text(rf.text(obs, ref)), show.rts(obs, r)}
        case _:
          show.rts(obs, r)

def show.rls(+obs: List<&2, Ob>, ls: List<&2, Rl>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, String, show.rts(obs, ts), show.rls(obs, t))

def show.strs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match t:
        case Nil{}:
          x
        case Con{h, r}:
          x ++ ", " ++ show.strs(Con{h, r})

def show.refs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " -> " ++ show.strs(Con{x, t})

def show.rds(+obs: List<&2, Ob>, +o: U32, rs: List<&2, Rd>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      match r:
        case Rd{i, nd, hd, ls}:
          "  " ++ text(rf.text(obs, in.ref(o, i))) ++ show.refs(List.append(&2, String, show.rts(obs, hd), show.rls(obs, ls))) ++ "\n" ++
            show.rds(obs, o, t)

# A module's copies
# -----------------

def cp.ers(c: Cp) -> List<&2, Er>:
  match c:
    case Cp{rds, ers, done}:
      ers

def cp.rds(c: Cp) -> List<&2, Rd>:
  match c:
    case Cp{rds, ers, done}:
      List.reverse(&2, Rd, rds)

# a concrete object and its copies
type Oc is Data:
  Oc{+id: U32, cp: Cp}

# every concrete object's copies, the root module's first and its alone;
# an abstract object's none
def module.copies(os: List<&2, Ob>, +cx: Cx) -> List<&2, Oc>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Oc>, Bool.not(U32.is_eq(loc.mod(no), 0)) || Bool.not(is.object(kind)), u => module.copies(t, cx),
            u => when(List<&2, Oc>, abs, v => Con{Oc{id, Cp{Nil{}, Nil{}, Nil{}}}, module.copies(t, cx)}, v => Con{Oc{id, copies(cx, id)}, module.copies(t, cx)}))

def ocs.ers(os: List<&2, Oc>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      match o:
        case Oc{+id, c}:
          List.append(&2, Er, cp.ers(c), ocs.ers(t))

def show.ocs(+obs: List<&2, Ob>, os: List<&2, Oc>) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, t}:
      match o:
        case Oc{+id, c}:
          when(String, is.root(obs, id), u => "module", u => show.abs.of(ob.abs(ob.at(obs, id))) ++ ob.name(obs, id)) ++ "\n" ++
            show.rds(obs, id, cp.rds(c)) ++ show.ocs(obs, t)

def er.same(a: Er, b: Er) -> Bool:
  match a b:
    case Er{+x, m} Er{+y, n}:
      U32.is_eq(x, y) && String.eq(m, n)

# sorted errors, each once: a body copied into several objects may raise
# one error in each
def ers.uniq(es: List<&2, Er>) -> List<&2, Er>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      match t:
        case Nil{}:
          [e]
        case Con{+f, +r}:
          when(List<&2, Er>, er.same(e, f), u => ers.uniq(Con{f, r}), u => Con{e, ers.uniq(Con{f, r})})

# a command's output: what it printed, and whether it found no error
# a file emission writes: its name, beside the root's, and its bytes
type Fo is Data:
  Fo{name: List<&2, U32>, bytes: List<&2, U32>}

# what a command prints, or the files emission writes
type Out is Type:
  Out{+ok: Bool, text: String}
  Outs{fs: List<&2, Fo>}

def ers.out(+files: List<&2, List<&2, U32>>, es: List<&2, Er>) -> Out:
  Out{False{}, show.ers(files, ers.uniq(List.sort(~Er, ~er.le, es)))}

def resolve.out(+files: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +os: List<&2, Oc>, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      Out{True{}, show.ocs(obs, os)}
    case Con{e, t}:
      ers.out(files, Con{e, t})

def resolved(+files: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +os: List<&2, Oc>) -> Out:
  resolve.out(files, obs, os, ocs.ers(os))

# Emission
# ========
#
# The emitted module (`blend-emit`): every copy a unit, the units in
# source order (the module's definitions and its concrete objects by
# their lines, an object's members in its linearization's order, its own
# first), emitted callees first by a walk from each in turn, every one
# emitted, so that a module imported by several is emitted once; two
# units calling each other an error,
# as Bend has no mutual recursion (`blend-adds-no-bend-logic`). Then the
# sharing: an affine unit has one use at most, a call to itself aside; a
# copied unit is emitted by its own name and once more for each use,
# `Obj.f.c1` and on in the order the uses are emitted
# (`blend-copies-keep-their-name`), the module's definitions calling it
# by its own name; an affine unit only a multiplied unit uses goes with
# each of its copies, numbered alike. The module's definitions are shared,
# as Bend's.

# a unit: one definition of the emitted program, before copies, and the
# concrete object it is emitted in
type Un is Data:
  Un{+o: U32, inst: In, node: Node, hd: List<&2, Rt>, ls: List<&2, Rl>}

def rf.eq(a: Rf, b: Rf) -> Bool:
  match a b:
    case Rf{+o1, n1, +p1, +g1} Rf{+o2, n2, +p2, +g2}:
      U32.is_eq(o1, o2) && same(n1, n2) && Bool.not(Bool.xor(p1, p2)) && (Bool.not(p1) || U32.is_eq(g1, g2))

def un.rds(+o: U32, rs: List<&2, Rd>) -> List<&2, Un>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case Rd{i, nd, hd, ls}:
          Con{Un{o, i, nd, hd, ls}, un.rds(o, t)}

def units(os: List<&2, Oc>) -> List<&2, Un>:
  match os:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case Oc{+id, c}:
          List.append(&2, Un, un.rds(id, cp.rds(c)), units(t))

def un.ref(u: Un) -> Rf:
  match u:
    case Un{+o, i, nd, hd, ls}:
      in.ref(o, i)

def node.what(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      what
    case _:
      0

def un.node(u: Un) -> Node:
  match u:
    case Un{+o, i, nd, hd, ls}:
      nd

# the units of one file: the code's (what 0) or the laws' and proofs'
def units.of(us: List<&2, Un>, +laws: Bool) -> List<&2, Un>:
  match us:
    case Nil{}:
      Nil{}
    case Con{+u, +t}:
      when(List<&2, Un>, Bool.not(Bool.xor(laws, U32.is_gt(node.what(un.node(u)), 0))), v => Con{u, units.of(t, laws)}, v => units.of(t, laws))

def un.hd(u: Un) -> List<&2, Rt>:
  match u:
    case Un{+o, i, nd, hd, ls}:
      hd

def un.lines(u: Un) -> List<&2, Rl>:
  match u:
    case Un{+o, i, nd, hd, ls}:
      ls

def un.or(m: Maybe<&2, Un>) -> Un:
  match m:
    case None{}:
      Un{0, In{Nil{}, 0, False{}}, NBad{Nil{}, 0}, Nil{}, Nil{}}
    case Some{u}:
      u

def un.at(+us: List<&2, Un>, +i: U32) -> Un:
  un.or(List.get(&2, Un, us, U32.to_nat(i)))

# a unit's index
def un.find(+us: List<&2, Un>, +r: Rf, +k: U32) -> Maybe<&2, U32>:
  match us:
    case Nil{}:
      None{}
    case Con{+u, +t}:
      when(Maybe<&2, U32>, rf.eq(un.ref(u), r), v => Some{k}, v => un.find(t, r, (k + 1 : U32)))

def node.no(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      no
    case _:
      0

def node.ind(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      ind
    case _:
      0

def node.share(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      share
    case _:
      0

def node.rest(n: Node) -> List<&2, U32>:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      rest
    case _:
      Nil{}

def un.name(+obs: List<&2, Ob>, +us: List<&2, Un>, +i: U32) -> List<&2, U32>:
  rf.text(obs, un.ref(un.at(us, i)))

# Uses
# ----

# a use: the unit used or using, and the line
type Ru is Data:
  Ru{+u: U32, +no: U32}

def refs.rts(ts: List<&2, Rt>, +us: List<&2, Un>, +self: U32, +no: U32) -> List<&2, Ru>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      match t:
        case RR{+mark, ref}:
          on.maybe(U32, List<&2, Ru>, un.find(us, ref, 0), v => refs.rts(r, us, self, no),
            +x => when(List<&2, Ru>, U32.is_eq(x, self), v => refs.rts(r, us, self, no), v => Con{Ru{x, no}, refs.rts(r, us, self, no)}))
        case _:
          refs.rts(r, us, self, no)

def refs.rls(ls: List<&2, Rl>, +us: List<&2, Un>, +self: U32) -> List<&2, Ru>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, Ru, refs.rts(ts, us, self, no), refs.rls(t, us, self))

# each unit's uses of others, in its body's order, calls to itself aside
def refss(xs: List<&2, Un>, +us: List<&2, Un>, +k: U32) -> List<&2, List<&2, Ru>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{List.append(&2, Ru, refs.rts(un.hd(x), us, k, node.no(un.node(x))), refs.rls(un.lines(x), us, k)), refss(t, us, (k + 1 : U32))}

def ru.us(rs: List<&2, Ru>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          Con{u, ru.us(t)}

def calls(rss: List<&2, List<&2, Ru>>) -> List<&2, List<&2, U32>>:
  match rss:
    case Nil{}:
      Nil{}
    case Con{rs, t}:
      Con{ru.us(rs), calls(t)}

def rus.or(m: Maybe<&2, List<&2, Ru>>) -> List<&2, Ru>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def rus.at(+rss: List<&2, List<&2, Ru>>, +i: U32) -> List<&2, Ru>:
  rus.or(List.get(&2, List<&2, Ru>, rss, U32.to_nat(i)))

# Order
# -----

# the units a source-order slot holds: a definition of the module's, or a
# concrete object
type Sl is Data:
  Sl{+no: U32, +kind: U32, name: List<&2, U32>, +id: U32}

def sl.le(a: Sl, b: Sl) -> Bool:
  match a b:
    case Sl{+x, +k1, n1, +i1} Sl{+y, +k2, n2, +i2}:
      U32.is_le(x, y)

def slots.mod(ns: List<&2, Node>) -> List<&2, Sl>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
          Con{Sl{no, 0, name, 0}, slots.mod(t)}
        case _:
          slots.mod(t)

def slots.obs(os: List<&2, Ob>) -> List<&2, Sl>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Sl>, abs || U32.is_eq(id, host) || Bool.not(U32.is_eq(loc.mod(no), 0)) || Bool.not(is.object(kind)), u => slots.obs(t),
            u => Con{Sl{no, 1, Nil{}, id}, slots.obs(t)})

# q's members that are o's finals, as references
def roots.q(ns: List<&2, Node>, +o: U32, +q: U32, +map: List<&2, En>) -> List<&2, Rf>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, +t}:
      match nd:
        case NDef{+share, +upd, +name, rest, params, body, +no, +ind, +what}:
          when(List<&2, Rf>, U32.is_eq(en.head(en.chain(en.find(map, name))), q),
            u => Con{Rf{o, name, False{}, o}, roots.q(t, o, q, map)}, u => roots.q(t, o, q, map))
        case _:
          roots.q(t, o, q, map)

def roots.ord(qs: List<&2, U32>, +cx: Cx, +o: U32) -> List<&2, Rf>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      List.append(&2, Rf, roots.q(ob.mems(ob.at(cx.obs(cx), q)), o, q, cx.map(cx, o)), roots.ord(t, cx, o))

def roots.sl(s: Sl, +cx: Cx) -> List<&2, Rf>:
  match s:
    case Sl{+no, +kind, name, +id}:
      match kind:
        case 0:
          [Rf{0, name, False{}, 0}]
        case _:
          roots.ord(cx.ord(cx, id), cx, id)

def roots.sls(ss: List<&2, Sl>, +cx: Cx) -> List<&2, Rf>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      List.append(&2, Rf, roots.sl(s, cx), roots.sls(t, cx))

def roots.ids(rs: List<&2, Rf>, +us: List<&2, Un>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, +t}:
      on.maybe(U32, List<&2, U32>, un.find(us, r, 0), u => roots.ids(t, us), x => Con{x, roots.ids(t, us)})

# every unit in source order
def roots.all(+cx: Cx, +us: List<&2, Un>) -> List<&2, U32>:
  roots.ids(roots.sls(List.sort(~Sl, ~sl.le, List.append(&2, Sl, slots.mod(ob.mems(ob.at(cx.obs(cx), 0))), slots.obs(cx.obs(cx)))), cx), us)

# The walk
# --------

# a unit being walked, and its calls not yet followed
type Fm is Data:
  Fm{+u: U32, rest: List<&2, U32>}

# the walk: its stack, the roots left, the units on the stack (the top
# first), those walked, the order (the last first), its errors; without
# a cycle, the order is those walked
type Ds is Data:
  Ds{stack: List<&2, Fm>, roots: List<&2, U32>, path: List<&2, U32>, done: List<&2, U32>, order: List<&2, U32>, ers: List<&2, Er>}

# every unit of xs in order
def all.in(xs: List<&2, U32>, +order: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      has(order, x) && all.in(t, order)

# an order, the last first, each unit's calls after it: emitted reversed,
# callees first, as Bend requires (blend/LAWS.bend, `order.callees_first`)
def ordered(xs: List<&2, U32>, +cal: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+u, +t}:
      all.in(ids.at(cal, u), t) && ordered(t, cal)

def path.to(ps: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      when(List<&2, U32>, U32.is_eq(p, c), u => [p], u => Con{p, path.to(t, c)})

def strs.and(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match t:
        case Nil{}:
          x
        case Con{y, r}:
          match r:
            case Nil{}:
              x ++ " and " ++ y
            case Con{z, r2}:
              x ++ ", " ++ strs.and(Con{y, Con{z, r2}})

def unit.names(xs: List<&2, U32>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{text(un.name(obs, us, x)), unit.names(t, obs, us)}

# units that call each other: those on the stack from c to the top
def er.cycle(+obs: List<&2, Ob>, +us: List<&2, Un>, +path: List<&2, U32>, +c: U32) -> Er:
  Er{node.no(un.node(un.at(us, c))),
    strs.and(unit.names(List.reverse(&2, U32, path.to(path, c)), obs, us)) ++ " call each other, which Bend cannot express"}

# a call followed: to a unit walked (seen), one on the stack (a cycle),
# else a unit pushed. Each step's choices are Bools a helper matches, so
# that a law can follow the walk (blend/LAWS.bend, `order`)
def ds.call.k(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, Fm>, +roots: List<&2, U32>, +path: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match seen cyc:
    case True{} _:
      Ds{Con{Fm{u, rs}, st}, roots, path, done, order, ers}
    case False{} True{}:
      Ds{Con{Fm{u, rs}, st}, roots, path, done, order, Con{er.cycle(obs, us, path, c), ers}}
    case False{} False{}:
      Ds{Con{Fm{c, ids.at(cal, c)}, Con{Fm{u, rs}, st}}, roots, Con{c, path}, done, order, ers}

def ds.call(+c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, Fm>, +roots: List<&2, U32>, +path: List<&2, U32>, +done: List<&2, U32>,
    +order: List<&2, U32>, +ers: List<&2, Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  ds.call.k(has(done, c), has(path, c), c, u, rs, st, roots, path, done, order, ers, cal, obs, us)

# a unit whose calls are all followed is walked, and joins the order
# once its callees have, so that the order is callee-first by
# computation (the law `order.callees_first` a case split); without a
# cycle they always have, and a cycle has been reported, so that a unit
# held back otherwise is a fault of Blend's walk
def ds.done.k(+ok: Bool, +u: U32, +st: List<&2, Fm>, +roots: List<&2, U32>, +path: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, Er>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match ok:
    case True{}:
      Ds{st, roots, List.tail(&2, U32, path), Con{u, done}, Con{u, order}, ers}
    case False{}:
      Ds{st, roots, List.tail(&2, U32, path), Con{u, done}, order,
        when(List<&2, Er>, List.is_empty(&2, Er, ers),
          w => [Er{node.no(un.node(un.at(us, u))), text(un.name(obs, us, u)) ++ ": Blend's walk reached it before its callees, a fault of Blend's"}],
          w => ers)}

def ds.done(+u: U32, +st: List<&2, Fm>, +roots: List<&2, U32>, +path: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, Er>,
    +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  ds.done.k(all.in(ids.at(cal, u), order), u, st, roots, path, done, order, ers, obs, us)

# a root, walked already (seen) or begun
def ds.root.k(+seen: Bool, +r: U32, +rt: List<&2, U32>, +path: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, Er>,
    +cal: List<&2, List<&2, U32>>) -> Ds:
  match seen:
    case True{}:
      Ds{Nil{}, rt, path, done, order, ers}
    case False{}:
      Ds{[Fm{r, ids.at(cal, r)}], rt, [r], done, order, ers}

def ds.step(s: Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match s:
    case Ds{stack, roots, path, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              Ds{Nil{}, Nil{}, path, done, order, ers}
            case Con{+r, +rt}:
              ds.root.k(has(done, r), r, rt, path, done, order, ers, cal)
        case Con{f, st}:
          match f:
            case Fm{+u, rest}:
              match rest:
                case Nil{}:
                  ds.done(u, st, roots, path, done, order, ers, cal, obs, us)
                case Con{+c, rs}:
                  ds.call(c, u, rs, st, roots, path, done, order, ers, cal, obs, us)

def ds.go(n: Nat, s: Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match n:
    case 0n:
      s
    case 1n+k:
      ds.go(k, ds.step(s, cal, obs, us), cal, obs, us)

def lens(xss: List<&2, List<&2, U32>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{xs, t}:
      Nat.add(List.length(&2, U32, xs), lens(t))

# the walk from the roots: each step pushes, pops or follows a call
def walk(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  ds.go(Nat.add(Nat.add(List.length(&2, U32, roots), lens(cal)), Nat.add(List.length(&2, Un, us), List.length(&2, Un, us))),
    Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}, Nil{}}, cal, obs, us)

# Sharing
# -------

# how a unit is emitted: by its own name, and m numbered copies more,
# numbered by its uses (copied, 1) or by its one user's copies (2); a
# plain unit (0) has none
type Mu is Data:
  Mu{+m: U32, +kind: U32}

def mu.or(x: Maybe<&2, Mu>) -> Mu:
  match x:
    case None{}:
      Mu{0, 0}
    case Some{v}:
      v

def mu.at(+ms: List<&2, Mu>, +i: U32) -> Mu:
  mu.or(List.get(&2, Mu, ms, U32.to_nat(i)))

def mu.m(x: Mu) -> U32:
  match x:
    case Mu{+m, +kind}:
      m

def mu.kind(x: Mu) -> U32:
  match x:
    case Mu{+m, +kind}:
      kind

def uses.in(rs: List<&2, Ru>, +e: U32, +x: U32) -> List<&2, Ru>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, +t}:
      match r:
        case Ru{+u, +no}:
          when(List<&2, Ru>, U32.is_eq(u, x), v => Con{Ru{e, no}, uses.in(t, e, x)}, v => uses.in(t, e, x))

# the uses of x by the emitted units, in their order
def uses.of(es: List<&2, U32>, +rss: List<&2, List<&2, Ru>>, +x: U32) -> List<&2, Ru>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      List.append(&2, Ru, uses.in(rus.at(rss, e), e, x), uses.of(t, rss, x))

def un.o(u: Un) -> U32:
  match u:
    case Un{+o, i, nd, hd, ls}:
      o

# the copies a copied unit's uses need: one for each copy of each user,
# its own name's included; none for the module's definitions, Bend's,
# which call it by its own name
def uses.m(rs: List<&2, Ru>, +ms: List<&2, Mu>, +us: List<&2, Un>) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          (when(U32, U32.is_eq(un.o(un.at(us, u)), 0), v => 0, v => (1 + mu.m(mu.at(ms, u)) : U32)) + uses.m(t, ms, us) : U32)

def ru.user(rs: List<&2, Ru>) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          u

def times(+n: U32) -> String:
  match n:
    case 1:
      ""
    case 2:
      ", twice"
    case _:
      ", " ++ U32.show(n) ++ " times"

# the uses grouped by user and line: `Obj.f (line 9, twice)`
def uses.say(rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +u: U32, +no: U32, +n: U32) -> List<&2, String>:
  match rs:
    case Nil{}:
      when(List<&2, String>, U32.is_eq(n, 0), v => Nil{},
        v => [text(un.name(obs, us, u)) ++ " (line " ++ U32.show(no) ++ times(n) ++ ")"])
    case Con{r, +t}:
      match r:
        case Ru{+v, +l}:
          when(List<&2, String>, (U32.is_eq(v, u) && U32.is_eq(l, no)) || U32.is_eq(n, 0), w => uses.say(t, obs, us, v, l, (n + 1 : U32)),
            w => Con{text(un.name(obs, us, u)) ++ " (line " ++ U32.show(no) ++ times(n) ++ ")", uses.say(t, obs, us, v, l, 1)})

def er.affine(+obs: List<&2, Ob>, +us: List<&2, Un>, +x: U32, +rs: List<&2, Ru>) -> Er:
  Er{node.no(un.node(un.at(us, x))), text(un.name(obs, us, x)) ++ " is affine and has " ++ U32.show(U32.from_nat(List.length(&2, Ru, rs))) ++
    " uses, in " ++ show.strs(uses.say(rs, obs, us, 0, 0, 0)) ++ ": mark it shared or copied"}

type Ms is Data:
  Ms{ms: List<&2, Mu>, ers: List<&2, Er>}

def ms.set(s: Ms, +x: U32, +mu: Mu) -> Ms:
  match s:
    case Ms{ms, ers}:
      Ms{List.set(&2, Mu, ms, U32.to_nat(x), mu), ers}

def ms.er(s: Ms, e: Er) -> Ms:
  match s:
    case Ms{ms, ers}:
      Ms{ms, Con{e, ers}}

def ms.ms(s: Ms) -> List<&2, Mu>:
  match s:
    case Ms{ms, ers}:
      ms

# an affine unit: plain when unused, the copies of its one user, an error
# when used twice
def mult.aff(n: Nat, +x: U32, +rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +s: Ms) -> Ms:
  match n:
    case 0n:
      s
    case 1n+k:
      match k:
        case 0n:
          when(Ms, U32.is_gt(mu.m(mu.at(ms.ms(s), ru.user(rs))), 0), v => ms.set(s, x, Mu{mu.m(mu.at(ms.ms(s), ru.user(rs))), 2}), v => s)
        case _:
          ms.er(s, er.affine(obs, us, x, rs))

# x's copies, its users' known: a copied unit's uses, an affine unit's one
# user's copies, an affine unit used twice an error
def mult.of(+x: U32, +share: U32, +rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +s: Ms) -> Ms:
  match share:
    case 1:
      s
    case 2:
      ms.set(s, x, Mu{uses.m(rs, ms.ms(s), us), 1})
    case _:
      mult.aff(List.length(&2, Ru, rs), x, rs, obs, us, s)

# from the last emitted to the first: each unit's users before it; the
# module's definitions shared, as Bend's
def mults(xs: List<&2, U32>, +es: List<&2, U32>, +rss: List<&2, List<&2, Ru>>, +obs: List<&2, Ob>, +us: List<&2, Un>, s: Ms) -> Ms:
  match xs:
    case Nil{}:
      s
    case Con{+x, t}:
      mults(t, es, rss, obs, us, mult.of(x, when(U32, U32.is_eq(un.o(un.at(us, x)), 0), u => 1, u => node.share(un.node(un.at(us, x)))),
        uses.of(es, rss, x), obs, us, s))

def mus.one(us: List<&2, Un>) -> List<&2, Mu>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      Con{Mu{0, 0}, mus.one(t)}

# Text
# ----

# what emission reads: the file's name, the objects, the units, how each
# is emitted
type Ec is Data:
  Ec{files: List<&2, List<&2, U32>>, obs: List<&2, Ob>, us: List<&2, Un>, mus: List<&2, Mu>, als: List<&2, Al>, own: List<&2, Ci>,
    res: List<&2, List<&2, U32>>, paths: List<&2, List<&2, U32>>, +mode: U32, rtypes: List<&2, List<&2, U32>>}

def ec.obs(e: Ec) -> List<&2, Ob>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      obs

def ec.us(e: Ec) -> List<&2, Un>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      us

def ec.mu(e: Ec, +i: U32) -> Mu:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      mu.at(mus, i)

# the text so far, its bytes reversed, and each copied unit's next number
type Tb is Data:
  Tb{acc: List<&2, U32>, ctrs: List<&2, U32>}

def rev.onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev.onto(t, Con{h, acc})

def tb.put(b: Tb, xs: List<&2, U32>) -> Tb:
  match b:
    case Tb{acc, ctrs}:
      Tb{rev.onto(xs, acc), ctrs}

def copy.name(base: List<&2, U32>, +j: U32) -> List<&2, U32>:
  List.append(&2, U32, base, List.append(&2, U32, codes(".c"), codes(U32.show(j))))

def unit.text(+e: Ec, +x: U32) -> List<&2, U32>:
  un.name(ec.obs(e), ec.us(e), x)

# a unit's own name in its j-th copy, the copy by its own name the 0th
def own.name(+e: Ec, +x: U32, +j: U32) -> List<&2, U32>:
  when(List<&2, U32>, U32.is_eq(j, 0), u => unit.text(e, x), u => copy.name(unit.text(e, x), j))

def ctr.or(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      1
    case Some{+x}:
      x

def ctr.at(+cs: List<&2, U32>, +i: U32) -> U32:
  ctr.or(List.get(&2, U32, cs, U32.to_nat(i)))

# the next of y's copies, counted
def ref.next(+e: Ec, +y: U32, b: Tb) -> Tb:
  match b:
    case Tb{acc, +ctrs}:
      Tb{rev.onto(copy.name(unit.text(e, y), ctr.at(ctrs, y)), acc), List.set(&2, U32, ctrs, U32.to_nat(y), (ctr.at(ctrs, y) + 1 : U32))}

# a use of y from x's j-th copy: y's own name, the next of y's copies, or
# the copy of y that goes with x's j-th; a definition of the module's
# calls y by its own name
def ref.kind(+kind: U32, +e: Ec, +x: U32, +y: U32, +j: U32, +b: Tb) -> Tb:
  match kind:
    case 0:
      tb.put(b, unit.text(e, y))
    case 1:
      when(Tb, U32.is_eq(un.o(un.at(ec.us(e), x)), 0), u => tb.put(b, unit.text(e, y)), u => ref.next(e, y, b))
    case _:
      tb.put(b, own.name(e, y, j))

def ref.self(+self: Bool, +e: Ec, +x: U32, +j: U32, +y: U32, b: Tb) -> Tb:
  match self:
    case True{}:
      tb.put(b, own.name(e, x, j))
    case False{}:
      ref.kind(mu.kind(ec.mu(e, y)), e, x, y, j, b)

def mark.put(+mark: U32, b: Tb) -> Tb:
  match mark:
    case 126:
      tb.put(b, [126])
    case _:
      b

def ec.als(e: Ec) -> List<&2, Al>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      als

def rf.obj(r: Rf) -> U32:
  match r:
    case Rf{+obj, name, +prior, +origin}:
      obj

# a reference outside the root module: its module's alias, then its name
def ci.path.find(cs: List<&2, Ci>, +p: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Ci{+alias, +path, +no}:
          when(Maybe<&2, List<&2, U32>>, same(path, p), u => Some{alias}, u => ci.path.find(t, p))

def res.index(ps: List<&2, List<&2, U32>>, +p: List<&2, U32>, +k: U32) -> U32:
  match ps:
    case Nil{}:
      k
    case Con{+x, t}:
      when(U32, same(x, p), u => k, u => res.index(t, p, (k + 1 : U32)))

def res.alias(+k: U32) -> List<&2, U32>:
  List.append(&2, U32, codes("Blend_"), codes(U32.show(k)))

# the file written: 0 the code, 1 the laws, 2 the proofs
def ec.mode(e: Ec) -> U32:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      mode

def ec.rtypes(e: Ec) -> List<&2, List<&2, U32>>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      rtypes

def ec.own(e: Ec) -> List<&2, Ci>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      own

def ec.res(e: Ec) -> List<&2, List<&2, U32>>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      res

def ec.paths(e: Ec) -> List<&2, List<&2, U32>>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      paths

# the alias the root's emission gives a file: the root's own import of it,
# else the one Blend reserves for it
def alias.of(+e: Ec, +p: List<&2, U32>) -> List<&2, U32>:
  on.maybe(List<&2, U32>, List<&2, U32>, ci.path.find(ec.own(e), p), u => res.alias((res.index(ec.res(e), p, 0) + 1 : U32)), x => x)

def mod.bend(+paths: List<&2, List<&2, U32>>, +m: U32) -> List<&2, U32>:
  bendify(path.at(paths, m), True{})

# a reference outside the root module: its module's alias, then its name
def rf.ext(+e: Ec, +r: Rf) -> List<&2, U32>:
  when(List<&2, U32>, U32.is_eq(loc.mod(ob.no(ob.at(ec.obs(e), rf.obj(r)))), 0), u => rf.text(ec.obs(e), r),
    u => List.append(&2, U32, alias.of(e, mod.bend(ec.paths(e), loc.mod(ob.no(ob.at(ec.obs(e), rf.obj(r)))))),
      Con{46, rf.text(ec.obs(e), r)}))

def un.what(+us: List<&2, Un>, +x: U32) -> U32:
  node.what(un.node(un.at(us, x)))

def rf.law(r: Rf) -> Rf:
  match r:
    case Rf{+obj, name, +prior, +origin}:
      Rf{obj, name.plain(name), False{}, origin}

# whether unit y is the law unit x proves, a prior proof's included: a
# proof's own law, named in its body, is the proof itself, its induction
# (any proof of a law serves, so none is bound late); another law named
# is that law's final proof
def proves.own(+us: List<&2, Un>, +x: U32, +y: U32) -> Bool:
  U32.is_eq(un.what(us, x), 2) && U32.is_eq(un.what(us, y), 1) && rf.eq(rf.law(un.ref(un.at(us, x))), un.ref(un.at(us, y)))

def ref.put(+e: Ec, +x: U32, +j: U32, +mark: U32, +r: Rf, m: Maybe<&2, U32>, +b: Tb) -> Tb:
  match m:
    case None{}:
      tb.put(mark.put(mark, b), when(List<&2, U32>, U32.is_gt(ec.mode(e), 0) && U32.is_eq(loc.mod(ob.no(ob.at(ec.obs(e), rf.obj(r)))), 0),
        u => List.append(&2, U32, codes("Blend_0."), rf.text(ec.obs(e), r)), u => rf.ext(e, r)))
    case Some{+y}:
      when(Tb, U32.is_eq(ec.mode(e), 2) && proves.own(ec.us(e), x, y),
        u => tb.put(mark.put(mark, b), List.append(&2, U32, codes("Blend_Laws."), own.name(e, x, j))),
        u => when(Tb, U32.is_eq(ec.mode(e), 2) && (U32.is_eq(un.what(ec.us(e), y), 1) || U32.is_eq(un.what(ec.us(e), y), 2)),
          v => tb.put(mark.put(mark, b), List.append(&2, U32, codes("Blend_Laws."), rf.text(ec.obs(e), r))),
          v => ref.self(U32.is_eq(y, x), e, x, j, y, mark.put(mark, b))))

# a token as written; in the laws and proofs, a datatype's or a
# constructor's name of the root's through the code's alias
def tok.in.proof(+e: Ec, t: Tok) -> List<&2, U32>:
  match t:
    case TName{+x}:
      when(List<&2, U32>, U32.is_gt(ec.mode(e), 0) && names.has(ec.rtypes(e), x), u => List.append(&2, U32, codes("Blend_0."), x), u => x)
    case _:
      tok.bytes(t)

def rts.put(ts: List<&2, Rt>, +e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  match ts:
    case Nil{}:
      b
    case Con{t, r}:
      match t:
        case RT{tk}:
          rts.put(r, e, x, j, tb.put(b, tok.in.proof(e, tk)))
        case RR{+mark, +ref}:
          rts.put(r, e, x, j, ref.put(e, x, j, mark, ref, un.find(ec.us(e), ref, 0), b))
        case RX{+mark, +path, +rest}:
          rts.put(r, e, x, j, tb.put(mark.put(mark, b), List.append(&2, U32, alias.of(e, path), Con{46, rest})))

def spaces(n: Nat) -> List<&2, U32>:
  List.replicate(U32, n, 32)

# a body line, its indentation the definition's subtracted; one written
# on its header's line (a type member's) stays on it
def rl.put(l: Rl, +e: Ec, +x: U32, +j: U32, +dind: U32, +b: Tb) -> Tb:
  match l:
    case Rl{+no, +ind, ts}:
      match ts:
        case Nil{}:
          tb.put(b, [10])
        case Con{t, r}:
          rts.put(Con{t, r}, e, x, j,
            when(Tb, U32.is_eq(no, node.no(un.node(un.at(ec.us(e), x)))), u => tb.put(b, [32]),
              u => tb.put(b, Con{10, spaces(U32.to_nat(when(U32, U32.is_gt(ind, dind), v => (ind - dind : U32), v => 0)))})))

def rls.put(ls: List<&2, Rl>, +e: Ec, +x: U32, +j: U32, +dind: U32, b: Tb) -> Tb:
  match ls:
    case Nil{}:
      b
    case Con{l, t}:
      rls.put(t, e, x, j, dind, rl.put(l, e, x, j, dind, b))

def ec.files(e: Ec) -> List<&2, List<&2, U32>>:
  match e:
    case Ec{files, obs, us, mus, als, own, res, paths, +mode, rtypes}:
      files

# the line before a definition naming where it is written,
# `# blend: FILE:LINE`: its body's lines follow as they do there, so the
# emitted line k lines below the marker is the source's k lines below
# LINE (blend/where.sh finds it)
def marker.at(+files: List<&2, List<&2, U32>>, +no: U32) -> List<&2, U32>:
  List.append(&2, U32, codes("\n# blend: "), List.append(&2, U32, loc.file(files, no), Con{58, codes(U32.show(loc.line(no)))}))

def marker(+e: Ec, +x: U32) -> List<&2, U32>:
  marker.at(ec.files(e), node.no(un.node(un.at(ec.us(e), x))))

# a definition's j-th copy, after a blank line: its marker,
# `def NAME(...) -> T:` and its body
# `law`, or a proof's `def` through the laws' alias, else `def` (a
# lemma's too)
def unit.kw(+e: Ec, +x: U32) -> List<&2, U32>:
  when(List<&2, U32>, U32.is_eq(un.what(ec.us(e), x), 1), u => codes("\nlaw "),
    u => when(List<&2, U32>, U32.is_eq(un.what(ec.us(e), x), 2), v => codes("\ndef Blend_Laws."), v => codes("\ndef ")))

# the unit whose lines a unit is written with: its own, but in the laws'
# file a proof's prior's, its law's
def unit.src(+e: Ec, +x: U32) -> U32:
  when(U32, U32.is_eq(ec.mode(e), 1) && U32.is_eq(un.what(ec.us(e), x), 2),
    u => on.maybe(U32, U32, un.find(ec.us(e), rf.law(un.ref(un.at(ec.us(e), x))), 0), v => x, y => y), u => x)

def node.params(n: Node) -> List<&2, List<&2, U32>>:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind, +what}:
      params
    case _:
      Nil{}

# a parameter passed on as Bend takes it: a template's `~f`, an erased
# one's `A` plainly
def arg.of(+p: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(p, [45]), u => List.tail(&2, U32, p), u => p)

def args.joined(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match t:
        case Nil{}:
          arg.of(p)
        case Con{h, r}:
          List.append(&2, U32, arg.of(p), List.append(&2, U32, codes(", "), args.joined(Con{h, r})))

def rf.name(r: Rf) -> List<&2, U32>:
  match r:
    case Rf{+obj, name, +prior, +origin}:
      name

# a witness's body: the object's own definition of the name, called with
# the declaration's parameters, the code's through `Blend_0`
def witness.body(+e: Ec, +x: U32) -> List<&2, U32>:
  when(List<&2, U32>, U32.is_eq(un.what(ec.us(e), x), 4),
    u => List.append(&2, U32, codes("\n  Blend_0."), List.append(&2, U32,
      path.name(ob.path(ob.at(ec.obs(e), rf.obj(un.ref(un.at(ec.us(e), x))))), name.plain(rf.name(un.ref(un.at(ec.us(e), x))))),
      Con{40, List.append(&2, U32, args.joined(node.params(un.node(un.at(ec.us(e), x)))), [41])})),
    u => Nil{})

def unit.put.as(+e: Ec, +s: U32, +x: U32, +j: U32, b: Tb) -> Tb:
  tb.put(rls.put(un.lines(un.at(ec.us(e), s)), e, s, j, node.ind(un.node(un.at(ec.us(e), s))),
    rts.put(un.hd(un.at(ec.us(e), s)), e, s, j,
      tb.put(b, List.append(&2, U32, marker(e, s), List.append(&2, U32, unit.kw(e, s), own.name(e, x, j)))))),
    List.append(&2, U32, witness.body(e, s), [10]))

def unit.put(+e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  unit.put.as(e, unit.src(e, x), x, j, b)

def copies.put(n: Nat, +e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  match n:
    case 0n:
      b
    case 1n+k:
      copies.put(k, e, x, (j + 1 : U32), unit.put(e, x, j, b))

# a unit by its own name, then its numbered copies
def unit.all(+e: Ec, +x: U32, +mu: Mu, b: Tb) -> Tb:
  match mu:
    case Mu{+m, +kind}:
      copies.put(U32.to_nat(m), e, x, 1, unit.put(e, x, 0, b))

def order.put(xs: List<&2, U32>, +e: Ec, b: Tb) -> Tb:
  match xs:
    case Nil{}:
      b
    case Con{+x, t}:
      order.put(t, e, unit.all(e, x, ec.mu(e, x), b))

# Imports
# -------
#
# The root's imports, a Blend one's path made the `.bend` it emits; then
# those its emission carries: a module whose objects' bodies it copies,
# or whose definitions it names, by the alias that module goes by, and the
# imports of a module it copies from, which those bodies name; each where
# the root has no import of that alias, an alias two imports give two
# files an error.

def im.line(i: Im) -> List<&2, U32>:
  match i:
    case Im{+path, +alias, +blend, +no}:
      List.append(&2, U32, codes("import "), List.append(&2, U32, bendify(path, blend), List.append(&2, U32, codes(" as "), alias)))

def imports(ns: List<&2, Node>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NImport{+txt, +no}:
          List.append(&2, U32, on.maybe(Im, List<&2, U32>, im.of(txt, no), u => txt, i => im.line(i)), Con{10, imports(t)})
        case _:
          imports(t)

def path.ups.rest(from: List<&2, List<&2, U32>>, to: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match from:
    case Nil{}:
      to
    case Con{f, t}:
      Con{codes(".."), path.ups.rest(t, to)}

def path.ups(from: List<&2, List<&2, U32>>, to: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  path.ups.rest(from, to)

# to's parts from the directory whose parts are from
def path.rel(from: List<&2, List<&2, U32>>, to: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match from to:
    case Con{+f, +ft} Con{+t, +tt}:
      when(List<&2, List<&2, U32>>, same(f, t), u => path.rel(ft, tt), u => path.ups(Con{f, ft}, Con{t, tt}))
    case _ _:
      path.ups.rest(from, to)

# a module's name in messages and markers: the root's file, the others'
# paths from the root's directory
def md.name(+root: List<&2, U32>, +path: List<&2, U32>) -> List<&2, U32>:
  slashes(path.rel(path.dir(root), split.slash(path, Nil{}, Nil{})))

# a path from the root's directory, as an import writes it
def rel.import(+root: List<&2, U32>, +path: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, starts(md.name(root, path), codes("..")), u => md.name(root, path), u => List.append(&2, U32, codes("./"), md.name(root, path)))

def need.rts(ts: List<&2, Rt>, +obs: List<&2, Ob>, +paths: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      match t:
        case RR{+mark, +ref}:
          when(List<&2, List<&2, U32>>, U32.is_eq(loc.mod(ob.no(ob.at(obs, rf.obj(ref)))), 0), u => need.rts(r, obs, paths),
            u => Con{mod.bend(paths, loc.mod(ob.no(ob.at(obs, rf.obj(ref))))), need.rts(r, obs, paths)})
        case RX{+mark, path, rest}:
          Con{path, need.rts(r, obs, paths)}
        case _:
          need.rts(r, obs, paths)

def need.rls(ls: List<&2, Rl>, +obs: List<&2, Ob>, +paths: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, List<&2, U32>, need.rts(ts, obs, paths), need.rls(t, obs, paths))

def need.us(us: List<&2, Un>, +obs: List<&2, Ob>, +paths: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      match u:
        case Un{+o, i, nd, hd, ls}:
          List.append(&2, List<&2, U32>, need.rts(hd, obs, paths), List.append(&2, List<&2, U32>, need.rls(ls, obs, paths), need.us(t, obs, paths)))

# each file once, in order, the root's own imports left out
def need.uniq(ps: List<&2, List<&2, U32>>, +own: List<&2, Ci>, +seen: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      when(List<&2, List<&2, U32>>, names.has(seen, p) || Maybe.is_some(&2, List<&2, U32>, ci.path.find(own, p)), u => need.uniq(t, own, seen),
        u => Con{p, need.uniq(t, own, Con{p, seen})})

# the reserved imports, `import ./lib/util.bend as Blend_1`
def res.lines(+root: List<&2, U32>, ps: List<&2, List<&2, U32>>, +k: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      List.append(&2, U32, codes("import "), List.append(&2, U32, rel.import(root, p),
        List.append(&2, U32, codes(" as "), List.append(&2, U32, res.alias(k), Con{10, res.lines(root, t, (k + 1 : U32))}))))

def zeros(us: List<&2, Un>) -> List<&2, U32>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      Con{1, zeros(t)}

# the text's bytes, its last newline kept
def tb.bytes(b: Tb) -> List<&2, U32>:
  match b:
    case Tb{acc, ctrs}:
      List.reverse(&2, U32, acc)

# the emitted module: its header, Bend's imports, each unit's copies in
# order
def bend.lines(ls: List<&2, Ln>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, txt}:
          Con{10, List.append(&2, U32, spaces(U32.to_nat(ind)), List.append(&2, U32, txt, bend.lines(t)))}

# the module's datatypes, Bend's, as written, each after a blank line and
# its marker
def datatypes(ns: List<&2, Node>, +files: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NBend{lines, +no}:
          List.append(&2, U32, marker.at(files, no), List.append(&2, U32, bend.lines(lines), Con{10, datatypes(t, files)}))
        case _:
          datatypes(t, files)

def module.bytes(+files: List<&2, List<&2, U32>>, +e: Ec, +order: List<&2, U32>, +tree: List<&2, Node>, +more: List<&2, U32>) -> List<&2, U32>:
  tb.bytes(order.put(order, e, Tb{rev.onto(List.append(&2, U32, codes("# Written by Blend from "),
    List.append(&2, U32, loc.file(files, 0), List.append(&2, U32, codes("; do not edit.\n"),
    List.append(&2, U32, imports(tree), List.append(&2, U32, more, datatypes(tree, files)))))), Nil{}), zeros(ec.us(e))}))

def ds.order(d: Ds) -> List<&2, U32>:
  match d:
    case Ds{stack, roots, path, done, order, ers}:
      order

def ds.ers(d: Ds) -> List<&2, Er>:
  match d:
    case Ds{stack, roots, path, done, order, ers}:
      ers

def ms.ers(s: Ms) -> List<&2, Er>:
  match s:
    case Ms{ms, ers}:
      ers

def file.stem(+b: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, ends(b, codes(".bend")), u => List.take(&2, U32, b, Nat.sub(List.length(&2, U32, b), 5n)), u => b)

# the root's file as Blend writes it, its last part given: `knet_LAWS.bend`
def root.file(+root: List<&2, U32>, +last: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, file.stem(bendify(List.head.or(List.reverse(&2, List<&2, U32>, split.slash(root, Nil{}, Nil{}))), True{})), last)

# the laws' file (mode 1) or the proofs' (mode 2): its context, its
# units in order, its reserved imports, its errors
type Pf is Data:
  Pf{e: Ec, order: List<&2, U32>, more: List<&2, U32>, ers: List<&2, Er>}

def pf.has(p: Pf) -> Bool:
  match p:
    case Pf{e, order, more, ers}:
      Bool.not(List.is_empty(&2, U32, order))

# the code's file, from beside it; the proofs import the laws' too, where
# there are laws
def code.import(+root: List<&2, U32>, +mode: U32, +laws: Bool) -> List<&2, U32>:
  List.append(&2, U32, codes("import ./"), List.append(&2, U32, root.file(root, codes(".bend")), List.append(&2, U32, codes(" as Blend_0\n"),
    when(List<&2, U32>, U32.is_eq(mode, 2) && laws, u => List.append(&2, U32, codes("import ./"), List.append(&2, U32, root.file(root, codes("_LAWS.bend")), codes(" as Blend_Laws\n"))),
      u => Nil{}))))

def proof.bytes(+files: List<&2, List<&2, U32>>, +e: Ec, +order: List<&2, U32>, +tree: List<&2, Node>, +more: List<&2, U32>, +laws: Bool) -> List<&2, U32>:
  tb.bytes(order.put(order, e, Tb{rev.onto(List.append(&2, U32, codes("# Written by Blend from "),
    List.append(&2, U32, loc.file(files, 0), List.append(&2, U32, codes("; do not edit.\n"),
    List.append(&2, U32, imports(tree), List.append(&2, U32, code.import(path.at(ec.paths(e), 0), ec.mode(e), laws), more))))), Nil{}), zeros(ec.us(e))}))

def pf.file(+files: List<&2, List<&2, U32>>, +tree: List<&2, Node>, +name: List<&2, U32>, +laws: Bool, p: Pf) -> Fo:
  match p:
    case Pf{+e, +order, more, ers}:
      Fo{name, proof.bytes(files, e, order, tree, more, laws)}

# the files, or the errors of any: the code; where the module has laws,
# the laws' beside it; where it has laws, proofs or witnesses, the
# proofs'; all of one emission (`blend-proofs-beside-code`)
def emit.out(+files: List<&2, List<&2, U32>>, +e: Ec, +order: List<&2, U32>, +tree: List<&2, Node>, +more: List<&2, U32>, +lw: Pf, +pf: Pf, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      Outs{Con{Fo{root.file(path.at(ec.paths(e), 0), codes(".bend")), module.bytes(files, e, List.reverse(&2, U32, order), tree, more)},
        List.append(&2, Fo,
          when(List<&2, Fo>, pf.has(lw), u => [pf.file(files, tree, root.file(path.at(ec.paths(e), 0), codes("_LAWS.bend")), True{}, lw)], u => Nil{}),
          when(List<&2, Fo>, pf.has(lw) || pf.has(pf), u => [pf.file(files, tree, root.file(path.at(ec.paths(e), 0), codes("_PROOF.bend")), pf.has(lw), pf)], u => Nil{}))}}
    case Con{x, t}:
      ers.out(files, Con{x, t})

# Names
# -----

# an emitted name, and the unit and line it is given for
type Nm is Data:
  Nm{name: List<&2, U32>, +u: U32, +no: U32}

def names.copies(n: Nat, +e: Ec, +x: U32, +j: U32) -> List<&2, Nm>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{Nm{own.name(e, x, j), x, node.no(un.node(un.at(ec.us(e), x)))}, names.copies(k, e, x, (j + 1 : U32))}

# every emitted definition's name, a unit's copies after it
def names.all(xs: List<&2, U32>, +e: Ec) -> List<&2, Nm>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      List.append(&2, Nm, names.copies(1n+U32.to_nat(mu.m(ec.mu(e, x))), e, x, 0), names.all(t, e))

def nm.find(ns: List<&2, Nm>, +n: List<&2, U32>) -> Maybe<&2, U32>:
  match ns:
    case Nil{}:
      None{}
    case Con{m, t}:
      match m:
        case Nm{+name, +u, +no}:
          when(Maybe<&2, U32>, same(name, n), v => Some{no}, v => nm.find(t, n))

# a name two definitions would be emitted by, a prior's or a copy's and a
# definition's whose name has dots (`tag.Plain` beside `_tag` from Plain)
def er.names(ns: List<&2, Nm>, +seen: List<&2, Nm>) -> List<&2, Er>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+m, +t}:
      match m:
        case Nm{+name, +u, +no}:
          on.maybe(U32, List<&2, Er>, nm.find(seen, name), v => er.names(t, Con{m, seen}),
            +l => Con{Er{no, text(name) ++ " would name two emitted definitions, those of lines " ++ U32.show(l) ++ " and " ++
              U32.show(no) ++ ": rename one"}, er.names(t, Con{m, seen})})

# a law, a proof or a lemma named where a definition is wanted: a law is
# a claim, and its proof and a lemma are Bend's alone to call
def er.law.rts(ts: List<&2, Rt>, +us: List<&2, Un>, +no: U32) -> List<&2, Er>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      match t:
        case RR{+mark, +ref}:
          on.maybe(U32, List<&2, Er>, un.find(us, ref, 0), v => er.law.rts(r, us, no),
            +x => when(List<&2, Er>, U32.is_eq(un.what(us, x), 0), v => er.law.rts(r, us, no),
              v => Con{Er{no, when(String, U32.is_eq(un.what(us, x), 1), w => "law " ++ text(rf.name(ref)) ++ " is a claim, not a definition",
                w => "proof " ++ text(name.plain(rf.name(ref))) ++ " belongs to the proofs, not the code") ++ ": only a proof may name it"}, er.law.rts(r, us, no)}))
        case _:
          er.law.rts(r, us, no)

def er.law.rls(ls: List<&2, Rl>, +us: List<&2, Un>) -> List<&2, Er>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, Er, er.law.rts(ts, us, no), er.law.rls(t, us))

# the laws' errors: a definition naming a law, a proof of no law
def er.laws(xs: List<&2, Un>, +us: List<&2, Un>) -> List<&2, Er>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, Er>, U32.is_eq(node.what(un.node(x)), 0),
        u => List.append(&2, Er, er.law.rts(un.hd(x), us, node.no(un.node(x))), List.append(&2, Er, er.law.rls(un.lines(x), us), er.laws(t, us))),
        u => when(List<&2, Er>, U32.is_eq(node.what(un.node(x)), 2) && Bool.not(on.maybe(U32, Bool, un.find(us, rf.law(un.ref(x)), 0), v => False{}, +y => U32.is_eq(un.what(us, y), 1))),
          v => Con{Er{node.no(un.node(x)), "proof " ++ text(name.plain(rf.name(un.ref(x)))) ++ " proves no law: its object states none of that name"}, er.laws(t, us)},
          v => er.laws(t, us)))

def pf.ers(p: Pf) -> List<&2, Er>:
  match p:
    case Pf{e, order, more, ers}:
      ers

def rf.proof(r: Rf) -> Rf:
  match r:
    case Rf{+obj, name, +prior, +origin}:
      Rf{obj, List.append(&2, U32, name, [35]), prior, origin}

# a unit's calls, a law called its proof's, unit k's own law left out
def calls.law(cs: List<&2, U32>, +us: List<&2, Un>, +k: U32) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, +t}:
      when(List<&2, U32>, proves.own(us, k, c), u => calls.law(t, us, k),
        u => when(List<&2, U32>, U32.is_eq(un.what(us, c), 1),
          v => on.maybe(U32, List<&2, U32>, un.find(us, rf.proof(un.ref(un.at(us, c))), 0), w => calls.law(t, us, k),
            +p => when(List<&2, U32>, U32.is_eq(p, k), w => calls.law(t, us, k), w => Con{p, calls.law(t, us, k)})),
          v => Con{c, calls.law(t, us, k)}))

def calls.laws(css: List<&2, List<&2, U32>>, +us: List<&2, Un>, +k: U32) -> List<&2, List<&2, U32>>:
  match css:
    case Nil{}:
      Nil{}
    case Con{cs, t}:
      Con{calls.law(cs, us, k), calls.laws(t, us, (k + 1 : U32))}

def rf.prior(r: Rf) -> Bool:
  match r:
    case Rf{+obj, name, +prior, +origin}:
      prior

# whether a unit goes in the laws' file (mode 1), its laws and its proofs'
# priors, each stating its law again by its own name, or the proofs'
# (mode 2), its proofs and lemmas
def un.in(+mode: U32, +u: Un) -> Bool:
  when(Bool, U32.is_eq(mode, 1),
    v => U32.is_eq(node.what(un.node(u)), 1) || (U32.is_eq(node.what(un.node(u)), 2) && rf.prior(un.ref(u))),
    v => U32.is_gt(node.what(un.node(u)), 1))

def units.what(us: List<&2, Un>, +mode: U32) -> List<&2, Un>:
  match us:
    case Nil{}:
      Nil{}
    case Con{+u, +t}:
      when(List<&2, Un>, un.in(mode, u), v => Con{u, units.what(t, mode)}, v => units.what(t, mode))

# the units of the order in a mode's file
def order.what(xs: List<&2, U32>, +us: List<&2, Un>, +mode: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, un.in(mode, un.at(us, x)), u => Con{x, order.what(t, us, mode)}, u => order.what(t, us, mode))

def proof.parts(+mode: U32, +files: List<&2, List<&2, U32>>, +cx: Cx, +all: List<&2, Un>) -> Pf:
  +obs = cx.obs(cx)
  +us = units.of(all, True{})
  +d = walk(roots.all(cx, us), calls.laws(calls(refss(us, us, 0)), us, 0), obs, us)
  +order = List.reverse(&2, U32, ds.order(d))
  +own = cis.of(ims.of(ob.mems(ob.at(obs, 0))), path.at(cx.paths(cx), 0))
  +res = need.uniq(need.us(units.what(us, mode), obs, cx.paths(cx)), own, Nil{})
  +e = {Ec{files, obs, us, mus.one(us), cx.als(cx), own, res, cx.paths(cx), mode, tree.types(ob.mems(ob.at(obs, 0)))} : Ec}
  Pf{e, order.what(order, us, mode), res.lines(path.at(cx.paths(cx), 0), res, 1),
    List.append(&2, Er, ds.ers(d), er.names(names.all(order.what(order, us, mode), e), Nil{}))}

# Stages
# ======
#
# A stage runs when the one before it found no error: the objects, the
# references, then emission.

# the emitted module, or its errors
def emitted(+files: List<&2, List<&2, U32>>, +cx: Cx, +os: List<&2, Oc>) -> Out:
  +obs = cx.obs(cx)
  +all = units(os)
  +us = units.of(all, False{})
  +rss = refss(us, us, 0)
  +d = walk(roots.all(cx, us), calls(rss), obs, us)
  +order = ds.order(d)
  +ms = mults(order, List.reverse(&2, U32, order), rss, obs, us, Ms{mus.one(us), Nil{}})
  +own = cis.of(ims.of(ob.mems(ob.at(obs, 0))), path.at(cx.paths(cx), 0))
  +res = need.uniq(need.us(us, obs, cx.paths(cx)), own, Nil{})
  +e = {Ec{files, obs, us, ms.ms(ms), cx.als(cx), own, res, cx.paths(cx), 0, Nil{}} : Ec}
  +lw = proof.parts(1, files, cx, all)
  +pf = proof.parts(2, files, cx, all)
  emit.out(files, e, order, ob.mems(ob.at(obs, 0)), res.lines(path.at(cx.paths(cx), 0), res, 1), lw, pf,
    List.append(&2, Er, ds.ers(d), List.append(&2, Er, ms.ers(ms), List.append(&2, Er, er.laws(all, all),
      List.append(&2, Er, er.names(names.all(List.reverse(&2, U32, order), e), Nil{}), List.append(&2, Er, pf.ers(lw), pf.ers(pf)))))))

# The laws and the proofs
# -----------------------
#
# A module's laws and proofs, each in a file of its own beside its code,
# as Bend's convention keeps them (`blend-proofs-beside-code`), so that
# the programs built carry none: `X_LAWS.bend` states the laws, the code
# `X.bend` imported as `Blend_0`; `X_PROOF.bend` proves them, importing
# both, the laws as `Blend_Laws`, each proof after those it uses (`_`,
# as Bend imports only plain names). A proof names the law it proves,
# which Bend reads as that law's proof.

def resolved.next(+cmd: U32, +files: List<&2, List<&2, U32>>, +cx: Cx, +os: List<&2, Oc>) -> Out:
  match cmd:
    case 3:
      resolved(files, cx.obs(cx), os)
    case _:
      when(Out, Maybe.is_some(&2, Er, List.head(&2, Er, ocs.ers(os))), u => resolved(files, cx.obs(cx), os),
        u => emitted(files, cx, os))

def objects.next(+cmd: U32, +files: List<&2, List<&2, U32>>, +als: List<&2, Al>, +paths: List<&2, List<&2, U32>>, +pss: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +fs: List<&2, Maybe<&2, Fd>>) -> Out:
  match cmd:
    case 2:
      Out{True{}, show.obs(obs, ls, fs, obs)}
    case _:
      resolved.next(cmd, files, Cx{obs, ls, fs, als, paths, pss}, module.copies(obs, Cx{obs, ls, fs, als, paths, pss}))

def objects.out(+cmd: U32, +files: List<&2, List<&2, U32>>, +als: List<&2, Al>, +paths: List<&2, List<&2, U32>>, +pss: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +fs: List<&2, Maybe<&2, Fd>>, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      objects.next(cmd, files, als, paths, pss, obs, ls, fs)
    case Con{e, t}:
      ers.out(files, Con{e, t})

def path.index(ps: List<&2, List<&2, U32>>, +p: List<&2, U32>, +k: U32) -> Maybe<&2, U32>:
  match ps:
    case Nil{}:
      None{}
    case Con{+x, t}:
      when(Maybe<&2, U32>, same(x, p), u => Some{k}, u => path.index(t, p, (k + 1 : U32)))

# module k's Blend imports as aliases; one no module was read for is the
# reader's error already
def als.mod(xs: List<&2, Im>, +k: U32, +paths: List<&2, List<&2, U32>>, +obs: List<&2, Ob>) -> List<&2, Al>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, +t}:
      match i:
        case Im{+path, +alias, +blend, +no}:
          on.maybe(U32, List<&2, Al>, path.index(paths, path.from(path.at(paths, k), path), 0), u => als.mod(t, k, paths, obs),
            +m => Con{Al{alias, root.find(obs, k), root.find(obs, m), no}, als.mod(t, k, paths, obs)})

def ims.blend(xs: List<&2, Im>) -> List<&2, Im>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+i, +t}:
      match i:
        case Im{path, alias, +blend, +no}:
          when(List<&2, Im>, blend && import.plain(path, codes(".blend")), u => Con{i, ims.blend(t)}, u => ims.blend(t))

# Paths
#
# A path's parts, split at `/`; `.` dropped and `..` taking the part before
# it, so that two spellings of one file are one module.

def als.all(ts: List<&2, List<&2, Node>>, +k: U32, +paths: List<&2, List<&2, U32>>, +obs: List<&2, Ob>) -> List<&2, Al>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{tr, t}:
      List.append(&2, Al, als.mod(ims.blend(ims.of(tr)), k, paths, obs), als.all(t, (k + 1 : U32), paths, obs))

def al.tos(als: List<&2, Al>, +from: U32) -> List<&2, U32>:
  match als:
    case Nil{}:
      Nil{}
    case Con{a, +t}:
      match a:
        case Al{name, +f, +to, +no}:
          when(List<&2, U32>, U32.is_eq(f, from), u => Con{to, al.tos(t, from)}, u => al.tos(t, from))

# whether target is reached from front by imports; fuel, the imports' count
# and one, as each module is followed once
def reach.go(n: Nat, +als: List<&2, Al>, front: List<&2, U32>, +seen: List<&2, U32>, +target: U32) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n++k:
      match front:
        case Nil{}:
          False{}
        case Con{+x, +t}:
          when(Bool, U32.is_eq(x, target), u => True{},
            u => when(Bool, has(seen, x), v => reach.go(k, als, t, seen, target),
              v => reach.go(k, als, List.append(&2, U32, t, al.tos(als, x)), Con{x, seen}, target)))

# an import that closes a cycle of imports: the module it imports reaches
# back to the one importing it
def er.cycles(xs: List<&2, Al>, +als: List<&2, Al>) -> List<&2, Er>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, +t}:
      match a:
        case Al{+name, +from, +to, +no}:
          when(List<&2, Er>, reach.go(2n+List.length(&2, Al, als), als, [to], Nil{}, from),
            u => Con{Er{no, "the import of " ++ text(name) ++ " closes a cycle of imports"}, er.cycles(t, als)},
            u => er.cycles(t, als))

# the names of the mixins whose host is q
def mixin.names.in(os: List<&2, Ob>, +q: U32) -> List<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, List<&2, U32>>, U32.is_eq(host, q) && Bool.not(is.object(kind)) && U32.is_eq(tpl, id),
            u => Con{path.last(path), mixin.names.in(t, q)}, u => mixin.names.in(t, q))

def names.fresh(ns: List<&2, List<&2, U32>>, +seen: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, +t}:
      when(List<&2, List<&2, U32>>, names.has(seen, n) || names.has(acc, n), u => names.fresh(t, seen, acc), u => Con{n, names.fresh(t, seen, Con{n, acc})})

# the names of the mixins of a linearization's objects, each once
def mixin.names(qs: List<&2, U32>, +obs: List<&2, Ob>, +seen: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      +ns = names.fresh(mixin.names.in(obs, ob.tpl(ob.at(obs, q))), seen, Nil{})
      List.append(&2, List<&2, U32>, ns, mixin.names(t, obs, List.append(&2, List<&2, U32>, ns, seen)))

# whether X.N is made already
def made.has(os: List<&2, Ob>, +x: U32, +n: List<&2, U32>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          (U32.is_eq(kind, 3) && U32.is_eq(host, x) && same(path.last(path), n)) || made.has(t, x, n)

# the nested objects to make for x: one for each name its mixins have
# that none is made for yet, numbered from next
def syn.x(ns: List<&2, List<&2, U32>>, +x: U32, +obs: List<&2, Ob>, +made: List<&2, Ob>, +next: U32) -> List<&2, Ob>:
  match ns:
    case Nil{}:
      made
    case Con{+n, +t}:
      when(List<&2, Ob>, made.has(obs, x, n) || made.has(made, x, n), u => syn.x(t, x, obs, made, next),
        u => syn.x(t, x, obs, Con{Ob{next, x, List.append(&2, List<&2, U32>, ob.path(ob.at(obs, x)), [n]), ob.abs(ob.at(obs, x)), Nil{}, Nil{},
          ob.no(ob.at(obs, x)), 3, next}, made}, (next + 1 : U32)))

# a round: for each object, its nested objects not yet made
def syn.round(os: List<&2, Ob>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +made: List<&2, Ob>) -> List<&2, Ob>:
  match os:
    case Nil{}:
      made
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Ob>, is.object(kind) && Bool.not(U32.is_eq(id, host)),
            u => syn.round(t, obs, ls, syn.x(mixin.names(lz.ord(lz.at(ls, id)), obs, Nil{}), id, obs, made,
              (U32.from_nat(List.length(&2, Ob, obs)) + U32.from_nat(List.length(&2, Ob, made)) : U32))),
            u => syn.round(t, obs, ls, made))

def copy.has(+os: List<&2, Ob>, +more: List<&2, Ob>, +t: U32, +x: U32) -> Bool:
  Maybe.is_some(&2, U32, copy.find(os, t, x)) || Maybe.is_some(&2, U32, copy.find(more, t, x))

# the copies x's mixins ts call for, bound to x: the template's members
# and line, its kind, x its host
def copies.t(ts: List<&2, U32>, +x: U32, +obs: List<&2, Ob>, +made: List<&2, Ob>, +next: U32) -> List<&2, Ob>:
  match ts:
    case Nil{}:
      made
    case Con{+t, +r}:
      when(List<&2, Ob>, copy.has(obs, made, t, x), u => copies.t(r, x, obs, made, next),
        u => copies.t(r, x, obs, Con{Ob{next, x, ob.path(ob.at(obs, t)), ob.abs(ob.at(obs, t)), Nil{}, ob.mems(ob.at(obs, t)), ob.no(ob.at(obs, t)),
          ob.kind(ob.at(obs, t)), t}, made}, (next + 1 : U32)))

# for each made object x.n, the copies its host's mixins of n call for
def syn.copies(os: List<&2, Ob>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +made: List<&2, Ob>) -> List<&2, Ob>:
  match os:
    case Nil{}:
      made
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Ob>, U32.is_eq(kind, 3),
            u => syn.copies(t, obs, ls, copies.t(mixins.of(lz.ord(lz.at(ls, host)), obs, path.last(path)), host, obs, made,
              (U32.from_nat(List.length(&2, Ob, obs)) + U32.from_nat(List.length(&2, Ob, made)) : U32))),
            u => syn.copies(t, obs, ls, made))

def pss.eq(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      same(x, y) && pss.eq(xt, yt)
    case _ _:
      False{}

type Sy is Data:
  Sy{obs: List<&2, Ob>, pss: List<&2, List<&2, U32>>, ls: List<&2, Maybe<&2, Lz>>}

def obs.none(os: List<&2, Ob>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, t}:
      False{}

# the rounds: the parents found with the linearizations of the round
# before, the linearizations, then the objects they call for; done when a
# round makes none and moves no parent; fuel, rounds enough for the
# deepest nesting twice over
def syn.go(n: Nat, +als: List<&2, Al>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>, +ls: List<&2, Maybe<&2, Lz>>) -> Sy:
  match n:
    case 0n:
      Sy{obs, pss, ls}
    case 1n++k:
      +npss = pids(obs, als, obs, ls)
      +nls = lins(npss)
      +made = syn.copies(obs, obs, nls, syn.round(obs, obs, nls, Nil{}))
      when(Sy, obs.none(made) && pss.eq(npss, pss), u => Sy{obs, npss, nls},
        u => syn.go(k, als, List.append(&2, Ob, obs, List.reverse(&2, Ob, made)), npss, nls))

def sy.obs(y: Sy) -> List<&2, Ob>:
  match y:
    case Sy{obs, pss, ls}:
      obs

def sy.pss(y: Sy) -> List<&2, List<&2, U32>>:
  match y:
    case Sy{obs, pss, ls}:
      pss

def sy.ls(y: Sy) -> List<&2, Maybe<&2, Lz>>:
  match y:
    case Sy{obs, pss, ls}:
      ls

def first.abs(+obs: List<&2, Ob>, ms: List<&2, U32>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{+m, t}:
      ob.abs(ob.at(obs, m))

# a made object abstract where its host is, or where the contributor
# nearest it says, as glam's `extend abstract` keeps abstract and its
# `extend` instantiates
def made.abs(os: List<&2, Ob>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>) -> List<&2, Ob>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no, +kind, +tpl}:
          Con{Ob{id, host, path, when(Bool, U32.is_eq(kind, 3), u => ob.abs(ob.at(obs, host)) || first.abs(obs, ids.at(pss, id)), u => abs),
            parents, mems, no, kind, tpl}, made.abs(t, obs, pss)}

def tpls(xs: List<&2, U32>, +obs: List<&2, Ob>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{ob.tpl(ob.at(obs, x)), tpls(t, obs)}

# a made object's parents that are mixins: its contributors, the parents
# of the one introducing it after them
def mixins.only(xs: List<&2, U32>, +obs: List<&2, Ob>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, is.object(ob.kind(ob.at(obs, x))), u => mixins.only(t, obs), u => Con{x, mixins.only(t, obs)})

# a nested object's contributors: the one furthest from it introduces N
# (`object N`), the rest extend it (`extend N`), as `def` and `upd`
def chain.check(ms: List<&2, U32>, +obs: List<&2, Ob>, +n: List<&2, U32>) -> List<&2, Er>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+m, +t}:
      match t:
        case Nil{}:
          when(List<&2, Er>, U32.is_eq(ob.kind(ob.at(obs, m)), 2),
            u => [Er{ob.no(ob.at(obs, m)), "extend " ++ text(n) ++ ": no " ++ text(n) ++ " is inherited here to extend (introduce one with `object " ++
              text(n) ++ "`)"}],
            u => Nil{})
        case Con{x, r}:
          List.append(&2, Er, when(List<&2, Er>, U32.is_eq(ob.kind(ob.at(obs, m)), 1),
            u => [Er{ob.no(ob.at(obs, m)), "object " ++ text(n) ++ ": another " ++ text(n) ++ " is inherited where this one is; extend it instead (`extend " ++
              text(n) ++ " with`)"}],
            u => Nil{}), chain.check(t, obs, n))

def blank.ers(es: List<&2, Er>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      False{}

# the made objects whose contributors are wrong
def chains.bad(os: List<&2, Ob>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, U32>, U32.is_eq(kind, 3) && Bool.not(blank.ers(chain.check(tpls(mixins.only(ids.at(pss, id), obs), obs), obs, path.last(path)))),
            u => Con{id, chains.bad(t, obs, pss)}, u => chains.bad(t, obs, pss))

def chains(os: List<&2, Ob>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Er>, U32.is_eq(kind, 3), u => List.append(&2, Er, chain.check(tpls(mixins.only(ids.at(pss, id), obs), obs), obs, path.last(path)), chains(t, obs, pss)),
            u => chains(t, obs, pss))

# the parents a nested object's introducing mixin names that name no
# object from a host it is made for
def er.made.parents(os: List<&2, Ob>, +als: List<&2, Al>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no, +kind, +tpl}:
          when(List<&2, Er>, U32.is_eq(kind, 3),
            u => on.maybe(U32, List<&2, Er>, last.id(mixins.of(lz.ord(lz.at(ls, host)), obs, path.last(path))), v => er.made.parents(t, als, obs, ls),
              +i => List.append(&2, Er, er.parents(ob.parents(ob.at(obs, i)), als, obs, i, host, ob.no(ob.at(obs, i))), er.made.parents(t, als, obs, ls))),
            u => er.made.parents(t, als, obs, ls))

# Modules
# =======
#
# A `.blend` file imports others, `import ./lib/x.blend as M`, each read
# once however many import it, its objects the same however reached
# (`blend-imports`): the command line reads the DAG of files from the
# root, a module a place, the root's 0, and each module's lines are
# numbered from its place times a million (Locations).

# the modules' objects (cmd 2), the root's copies (3) or the root module
# emitted (4), or the errors of the first stage that has them, each
# `FILE:LINE: message`

# Modules
# =======
#
# A `.blend` file imports others, `import ./lib/x.blend as M`, each read
# once however many import it, its objects the same however reached
# (`blend-imports`): the command line reads the DAG of files from the
# root, a module a place, the root's 0, and each module's lines are
# numbered from its place times a million (Locations).

# the modules' objects (cmd 2), the root's copies (3) or the root module
# emitted (4), or the errors of the first stage that has them, each
# `FILE:LINE: message`
def objects(+cmd: U32, +files: List<&2, List<&2, U32>>, +paths: List<&2, List<&2, U32>>, +trees: List<&2, List<&2, Node>>) -> Out:
  +obs0 = obs(trees)
  +als = als.all(trees, 0, paths, obs0)
  +sy = syn.go(Nat.add(2n, Nat.add(List.length(&2, Ob, obs0), List.length(&2, Ob, obs0))), als, obs0, Nil{}, Nil{})
  +pss = sy.pss(sy)
  +ls = sy.ls(sy)
  +obs = made.abs(sy.obs(sy), sy.obs(sy), pss)
  +fs = folds(ls, obs, chains.bad(obs, obs, pss))
  objects.out(cmd, files, als, paths, pss, obs, ls, fs,
    List.append(&2, Er, er.cycles(als, als), List.append(&2, Er, chains(obs, obs, pss), 
      List.append(&2, Er, er.obs(obs, als, obs), List.append(&2, Er, er.made.parents(obs, als, obs, ls),
      List.append(&2, Er, er.lins(pss, ls, 0, obs, ls), er.defs(pss, fs, ls, 0, obs, fs)))))))

# Nested objects
# --------------
#
# A nested object as written, `object N` (kind 1), and an extension,
# `extend N with` (kind 2), are mixins (blend-nested): for an object X
# and a name N some objects of X's linearization hold mixins of, X.N is
# an object of its own (kind 3), host X, its parents those mixins in X's
# linearization's order, then the parents the one introducing N names,
# found from X, so that C3 gives the contributors from X's end to the
# introducer, then those parents: N folded down X's linearization as a
# definition is, `object N` introducing it and `extend N` updating it,
# glam's `extend` a mixin on the named object. X.N binds its own copy of
# each mixin to X, an identity of its own in C3: their bodies' `^` is
# X's, never bound again (blend-frozen-host).
# Made in rounds, as X.N's own nested objects come of its mixins'
# children and a parent may name a nested object made in a round before;
# until a round makes no object and moves no parent.

# a module read: its path from where the root was read, its bytes, whether
# it was read, and the import line that first reached it
type Md is Data:
  Md{path: List<&2, U32>, bs: List<&2, U32>, +ok: Bool, +from: U32}

def mds.has(ms: List<&2, Md>, +p: List<&2, U32>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, t}:
      match m:
        case Md{path, bs, +ok, +from}:
          same(path, p) || mds.has(t, p)

# a module still to read, and the import line reaching it
type Td is Data:
  Td{path: List<&2, U32>, +from: U32}

# the Blend imports of a module read, as paths from where the root was
def tds.of(+path: List<&2, U32>, xs: List<&2, Im>) -> List<&2, Td>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      match i:
        case Im{p, alias, +blend, +no}:
          Con{Td{path.from(path, p), no}, tds.of(path, t)}

# the modules a module read imports, its lines numbered for place k
def md.next(+path: List<&2, U32>, +bs: List<&2, U32>, +k: U32) -> List<&2, Td>:
  tds.of(path, ims.blend(ims.of(read.at(bs, (k * 1000000 : U32)))))

def md.path(m: Md) -> List<&2, U32>:
  match m:
    case Md{path, bs, +ok, +from}:
      path

def mds.paths(ms: List<&2, Md>) -> List<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{md.path(m), mds.paths(t)}

def mds.names(ms: List<&2, Md>, +root: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{md.name(root, md.path(m)), mds.names(t, root)}

def mds.trees(ms: List<&2, Md>, +k: U32) -> List<&2, List<&2, Node>>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      match m:
        case Md{path, bs, +ok, +from}:
          Con{read.at(bs, (k * 1000000 : U32)), mds.trees(t, (k + 1 : U32))}

# the modules an import reached but none could read
def mds.ers(ms: List<&2, Md>, +root: List<&2, U32>) -> List<&2, Er>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, +t}:
      match m:
        case Md{path, bs, +ok, +from}:
          when(List<&2, Er>, ok, u => mds.ers(t, root), u => Con{Er{from, "cannot read " ++ text(md.name(root, path))}, mds.ers(t, root)})

def tree.root(ts: List<&2, List<&2, Node>>) -> List<&2, Node>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x

def md.bs(m: Md) -> List<&2, U32>:
  match m:
    case Md{path, bs, +ok, +from}:
      bs

def md.ok(m: Md) -> Bool:
  match m:
    case Md{path, bs, +ok, +from}:
      ok

# The command line
# ================
#
#   bend blend.bend read FILE.blend       the structure (`blend-read`)
#   bend blend.bend objects FILE.blend    the objects, or the errors found
#                                         so far, `FILE:LINE: message`
#                                         in line order (`blend-objects`)
#   bend blend.bend resolve FILE.blend    each concrete object's copies
#                                         and what their names reach
#                                         (`blend-resolve`)
#   bend blend.bend emit FILE.blend       the emitted module, every
#                                         concrete object's definitions
#                                         (`blend-emit`)
#
# blend/run.sh runs the same, built once (blend/build.sh).

def base.k(r: List<&2, U32> & List<&2, U32>) -> String:
  (a, b) = r
  text(List.reverse(&2, U32, a))

# a path's last part, as messages name the file
def basename(path: String) -> String:
  base.k(until(List.reverse(&2, U32, codes(path)), 47))

def usage() -> String:
  "usage: bend blend.bend read|objects|resolve FILE.blend, or emit [--alone] FILE.blend... [DIR]"

# 1 read, 2 objects, 3 resolve, 4 emit
def run(+cmd: U32, +files: List<&2, List<&2, U32>>, +paths: List<&2, List<&2, U32>>, +trees: List<&2, List<&2, Node>>) -> Out:
  match cmd:
    case 1:
      Out{True{}, show(tree.root(trees), 1n+count(tree.root(trees)))}
    case 0:
      Out{False{}, usage()}
    case _:
      objects(cmd, files, paths, trees)

def ims.plain.ers(xs: List<&2, Im>) -> List<&2, Er>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      List.append(&2, Er, im.plain.ers(i), ims.plain.ers(t))

# each module's Blend imports whose paths Bend would refuse
def trees.plain.ers(ts: List<&2, List<&2, Node>>) -> List<&2, Er>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      List.append(&2, Er, ims.plain.ers(ims.of(x)), trees.plain.ers(t))

# the modules' errors as read: an import none could read, one whose path
# Bend would refuse
def load.ers(+r: Md, +t: List<&2, Md>) -> List<&2, Er>:
  List.append(&2, Er, mds.ers(t, md.path(r)), trees.plain.ers(mds.trees(Con{r, t}, 0)))

# a command over the modules read, the root first; the modules' errors as
# read first
def run.mods(+cmd: U32, +ms: List<&2, Md>) -> Out:
  match ms:
    case Nil{}:
      Out{False{}, usage()}
    case Con{+r, +t}:
      when(Out, md.ok(r),
        u => when(Out, Maybe.is_some(&2, Er, List.head(&2, Er, load.ers(r, t))),
          v => ers.out(mds.names(Con{r, t}, md.path(r)), load.ers(r, t)),
          v => run(cmd, mds.names(Con{r, t}, md.path(r)), mds.paths(Con{r, t}), mds.trees(Con{r, t}, 0))),
        u => Out{False{}, "blend: cannot read " ++ text(md.path(r))})

def write.done(fr: File & Result<&1, &1, U32 & String, Unit>) -> IO(Bool):
  (f, r) = fr
  match r:
    case Done{u}:
      do IO<Bool>:
        File.close(f)
        return True{}
    case Fail{e}:
      do IO<Bool>:
        File.close(f)
        return False{}

def write.opened(r: Result<&1, &1, U32 & String, File>, bs: List<&2, U32>) -> IO(Bool):
  match r:
    case Done{f}:
      do IO<Bool>:
        fr : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, bs)
        write.done(fr)
    case Fail{e}:
      IO.pure(Bool, False{})

# a file's bytes written, False where it cannot be
def write.file(+path: List<&2, U32>, bs: List<&2, U32>) -> IO(Bool):
  do IO<Bool>:
    r : Result<&1, &1, U32 & String, File> <- File.open_bytes(path, "w")
    write.opened(r, bs)

def path.join(+dir: List<&2, U32>, +name: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, dir, Con{47, name})

def write.failed(+path: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    IO.print_err("blend: cannot write " ++ text(path))
    IO.exit(1)

# the files written, each path printed once written
def write.all(fs: List<&2, Fo>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{f, t}:
      match f:
        case Fo{+path, bs}:
          IO.bind(Bool, Unit, write.file(path, bs),
            +ok => when(IO(Unit), ok, u => IO.bind(Unit, Unit, IO.print(text(path)), v => write.all(t)), u => write.failed(path)))

def fos.at(fs: List<&2, Fo>, +dir: List<&2, U32>) -> List<&2, Fo>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Fo{+name, bs}:
          Con{Fo{path.join(dir, name), bs}, fos.at(t, dir)}

# a module's files placed in dir
def out.at(o: Out, +dir: List<&2, U32>) -> Out:
  match o:
    case Outs{fs}:
      Outs{fos.at(fs, dir)}
    case Out{+ok, text}:
      Out{ok, text}

# two modules' emissions as one: their files, or the errors of either
# and both, so that a command writes every module's files or none
def out.join(a: Out, b: Out) -> Out:
  match a b:
    case Outs{x} Outs{y}:
      Outs{List.append(&2, Fo, x, y)}
    case Outs{x} Out{+ok, t}:
      Out{False{}, t}
    case Out{+ok, t} Outs{y}:
      Out{False{}, t}
    case Out{+ok1, t1} Out{+ok2, t2}:
      Out{False{}, t1 ++ "\n" ++ t2}

def fos.twice(fs: List<&2, Fo>, +seen: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, t}:
      match f:
        case Fo{+path, bs}:
          when(Maybe<&2, List<&2, U32>>, names.has(seen, path), u => Some{path}, u => fos.twice(t, Con{path, seen}))

# the files, unless two modules would write one path
def out.once(o: Out) -> Out:
  match o:
    case Outs{+fs}:
      on.maybe(List<&2, U32>, Out, fos.twice(fs, Nil{}), u => Outs{fs}, +p => Out{False{}, "blend: two modules would write " ++ text(p)})
    case Out{+ok, text}:
      Out{ok, text}

# the output printed, or the files written; errors to stderr, and the
# exit status 1
def main.out(o: Out) -> IO(Unit):
  match o:
    case Out{+ok, text}:
      match ok:
        case True{}:
          IO.print(text)
        case False{}:
          do IO<Unit>:
            IO.print_err(text)
            IO.exit(1)
    case Outs{fs}:
      write.all(fs)

def read.got(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Maybe<&2, List<&2, U32>>):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Maybe<&2, List<&2, U32>>>:
        File.close(f)
        return Some{bs}
    case Fail{e}:
      do IO<Maybe<&2, List<&2, U32>>>:
        File.close(f)
        return None{}

def read.sized(fs: File & Result<&1, &1, U32 & String, U32>) -> IO(Maybe<&2, List<&2, U32>>):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Maybe<&2, List<&2, U32>>>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        read.got(fr)
    case Fail{e}:
      do IO<Maybe<&2, List<&2, U32>>>:
        File.close(f)
        return None{}

def read.opened(r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, List<&2, U32>>):
  match r:
    case Done{f}:
      do IO<Maybe<&2, List<&2, U32>>>:
        fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        read.sized(fs)
    case Fail{e}:
      IO.pure(Maybe<&2, List<&2, U32>>, None{})

# a file's bytes, None where it cannot be read
def read.file(+path: List<&2, U32>) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    r : Result<&1, &1, U32 & String, File> <- File.open_bytes(path, "r")
    read.opened(r)

def md.of(+path: List<&2, U32>, m: Maybe<&2, List<&2, U32>>, +from: U32) -> Md:
  match m:
    case None{}:
      Md{path, Nil{}, False{}, from}
    case Some{bs}:
      Md{path, bs, True{}, from}

def md.todo(+path: List<&2, U32>, m: Maybe<&2, List<&2, U32>>, +k: U32) -> List<&2, Td>:
  match m:
    case None{}:
      Nil{}
    case Some{+bs}:
      md.next(path, bs, k)

# the modules, breadth first from the root, each once; fuel, the files
# read at most
def load.go(n: Nat, todo: List<&2, Td>, +mods: List<&2, Md>) -> IO(List<&2, Md>):
  match n:
    case 0n:
      IO.pure(List<&2, Md>, List.reverse(&2, Md, mods))
    case 1n++k:
      match todo:
        case Nil{}:
          IO.pure(List<&2, Md>, List.reverse(&2, Md, mods))
        case Con{td, +rest}:
          match td:
            case Td{+path, +from}:
              when(IO(List<&2, Md>), mds.has(mods, path), u => load.go(k, rest, mods),
                u => IO.bind(Maybe<&2, List<&2, U32>>, List<&2, Md>, read.file(path),
                  +m => load.go(k, List.append(&2, Td, rest, md.todo(path, m, U32.from_nat(List.length(&2, Md, mods)))),
                    Con{md.of(path, m, from), mods})))

def main.file(+cmd: U32, +path: String) -> IO(Unit):
  do IO<Unit>:
    ms : List<&2, Md> <- load.go(4096n, [Td{codes(path), 0}], Nil{})
    main.out(run.mods(cmd, ms))

# a path's directory, `.` for a bare name
def dir.of(+p: List<&2, U32>) -> List<&2, U32>:
  when(List<&2, U32>, holds(p, [47]), u => slashes(path.dir(p)), u => codes("."))

def dir.or(m: Maybe<&2, List<&2, U32>>, +p: List<&2, U32>) -> List<&2, U32>:
  match m:
    case None{}:
      dir.of(p)
    case Some{d}:
      d

# Imports not named
# ------------------
#
# A command writes the modules it names; a module they import, named
# nowhere, is not written (a package's, once packages come, never), but
# verified: emitted again in memory and compared with its files beside
# it, each byte. A file stale, missing, or no longer emitted is an error,
# and the command writes nothing; `--alone` leaves the imports unverified.

# a check of a file: its path, the module emitting it, and its bytes, or
# none where it must not be; or an error found already
type Ck is Data:
  Ck{path: List<&2, U32>, src: List<&2, U32>, want: Maybe<&2, List<&2, U32>>}
  Cer{msg: List<&2, U32>}

def ck.line(+path: List<&2, U32>, +what: List<&2, U32>, +src: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, codes("blend: "), List.append(&2, U32, path, List.append(&2, U32, what, List.append(&2, U32, src, codes("\n")))))

# what a check finds: nothing where the file is as it must be
def ck.msg(+path: List<&2, U32>, +src: List<&2, U32>, want: Maybe<&2, List<&2, U32>>, got: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match want got:
    case Some{w} Some{g}:
      when(List<&2, U32>, same(w, g), u => Nil{}, u => ck.line(path, codes(" is stale: it is not what "), List.append(&2, U32, src, codes(" emits"))))
    case Some{w} None{}:
      ck.line(path, codes(" is missing, which "), List.append(&2, U32, src, codes(" emits")))
    case None{} Some{g}:
      ck.line(path, codes(" is stale: "), List.append(&2, U32, src, codes(" emits it no longer")))
    case None{} None{}:
      Nil{}

def cks.of(fs: List<&2, Fo>, +src: List<&2, U32>) -> List<&2, Ck>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Fo{path, bs}:
          Con{Ck{path, src, Some{bs}}, cks.of(t, src)}

def fos.named(fs: List<&2, Fo>, +n: List<&2, U32>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, t}:
      match f:
        case Fo{name, bs}:
          same(name, n) || fos.named(t, n)

# a laws or proofs file the module emits not, which must not be
def ck.gone(+fs: List<&2, Fo>, +d: List<&2, U32>, +last: List<&2, U32>) -> List<&2, Ck>:
  when(List<&2, Ck>, fos.named(fs, root.file(d, last)), u => Nil{}, u => [Ck{path.join(dir.of(d), root.file(d, last)), d, None{}}])

# the checks of an import's files, from its emission
def dep.checks(o: Out, +d: List<&2, U32>) -> List<&2, Ck>:
  match o:
    case Outs{+fs}:
      List.append(&2, Ck, cks.of(fos.at(fs, dir.of(d)), d),
        List.append(&2, Ck, ck.gone(fs, d, codes("_LAWS.bend")), ck.gone(fs, d, codes("_PROOF.bend"))))
    case Out{+ok, text}:
      [Cer{List.append(&2, U32, codes("blend: "), List.append(&2, U32, d, List.append(&2, U32, codes(", which it imports, has errors of its own:\n"),
        List.append(&2, U32, codes(text), codes("\n")))))}]

# every import, once, that no argument names
def deps.missed(ds: List<&2, List<&2, U32>>, +named: List<&2, List<&2, U32>>, +seen: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, +t}:
      when(List<&2, List<&2, U32>>, names.has(named, d) || names.has(seen, d), u => deps.missed(t, named, seen),
        u => Con{d, deps.missed(t, named, Con{d, seen})})

def verify.end(+errs: List<&2, U32>, fs: List<&2, Fo>) -> IO(Unit):
  when(IO(Unit), List.is_empty(&2, U32, errs), u => write.all(fs),
    u => do IO<Unit>:
      IO.print_err(text(errs) ++ "blend: name each such import too, or emit --alone to leave the imports unverified")
      IO.exit(1))

# the checks made in turn, each file read and compared; then the files
# written, or the errors found and nothing written
def verify.cks(cks: List<&2, Ck>, +errs: List<&2, U32>, fs: List<&2, Fo>) -> IO(Unit):
  match cks:
    case Nil{}:
      verify.end(errs, fs)
    case Con{c, ct}:
      match c:
        case Ck{+path, +src, want}:
          IO.bind(Maybe<&2, List<&2, U32>>, Unit, read.file(path),
            +m => verify.cks(ct, List.append(&2, U32, errs, ck.msg(path, src, want, m)), fs))
        case Cer{msg}:
          verify.cks(ct, List.append(&2, U32, errs, msg), fs)

# each import emitted again in memory, its checks gathered; then made
def verify.deps(ds: List<&2, List<&2, U32>>, acc: List<&2, Ck>, fs: List<&2, Fo>) -> IO(Unit):
  match ds:
    case Nil{}:
      verify.cks(acc, Nil{}, fs)
    case Con{+d, dt}:
      IO.bind(List<&2, Md>, Unit, load.go(4096n, [Td{d, 0}], Nil{}),
        +ms => verify.deps(dt, List.append(&2, Ck, acc, dep.checks(run.mods(4, ms), d)), fs))

def emit.end(+alone: Bool, ds: List<&2, List<&2, U32>>, o: Out) -> IO(Unit):
  match o:
    case Outs{+fs}:
      when(IO(Unit), alone, u => write.all(fs), u => verify.deps(ds, Nil{}, fs))
    case Out{+ok, text}:
      main.out(Out{ok, text})

# each module emitted in turn, each read with its imports, into the
# directory given, else its own; then the imports none names verified,
# unless alone; then every module's files written, or none
def main.emit.go(ps: List<&2, String>, +dir: Maybe<&2, List<&2, U32>>, +alone: Bool, +named: List<&2, List<&2, U32>>, deps: List<&2, List<&2, U32>>, acc: Out) -> IO(Unit):
  match ps:
    case Nil{}:
      emit.end(alone, deps.missed(deps, named, Nil{}), out.once(acc))
    case Con{+p, t}:
      IO.bind(List<&2, Md>, Unit, load.go(4096n, [Td{codes(p), 0}], Nil{}),
        +ms => main.emit.go(t, dir, alone, named, List.append(&2, List<&2, U32>, deps, List.tail(&2, List<&2, U32>, mds.paths(ms))),
          out.join(acc, out.at(run.mods(4, ms), dir.or(dir, codes(p))))))

def args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, args.data(t)}

def args.plain(xs: List<&2, String>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{path.plain(codes(x)), args.plain(t)}

def args.dashed(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      starts(codes(x), [45]) || args.dashed(t)

def main.emit.at(+alone: Bool, +srcs: List<&2, String>, +dir: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  main.emit.go(srcs, dir, alone, args.plain(srcs), Nil{}, Outs{Nil{}})

# the modules, and a last argument not one the directory
def main.emit.k(+alone: Bool, +xs: List<&2, String>) -> IO(Unit):
  on.maybe(String, IO(Unit), List.last(&2, String, xs), u => main.out(Out{False{}, usage()}),
    +l => when(IO(Unit), args.dashed(xs), v => main.out(Out{False{}, usage()}),
      v => when(IO(Unit), Bool.not(ends(codes(l), codes(".blend"))) && Nat.is_gt(List.length(&2, String, xs), 1n),
        w => main.emit.at(alone, List.take(&2, String, xs, Nat.sub(List.length(&2, String, xs), 1n)), Some{codes(l)}),
        w => main.emit.at(alone, xs, None{}))))

# `emit [--alone] FILE.blend... [DIR]`
def main.emit(+xs: List<&2, String>) -> IO(Unit):
  on.maybe(String, IO(Unit), List.head(&2, String, xs), u => main.out(Out{False{}, usage()}),
    +h => when(IO(Unit), String.eq(h, "--alone"), v => main.emit.k(True{}, List.tail(&2, String, xs)), v => main.emit.k(False{}, xs)))

def main.cmd(+cmd: U32, xs: List<String>) -> IO(Unit):
  match cmd:
    case 0:
      main.out(Out{False{}, usage()})
    case 4:
      main.emit(args.data(xs))
    case _:
      match xs:
        case Con{+path, r}:
          match r:
            case Nil{}:
              main.file(cmd, path)
            case Con{d, t}:
              main.out(Out{False{}, usage()})
        case Nil{}:
          main.out(Out{False{}, usage()})

def cmd.of(+rd: Bool, +ob: Bool, +rs: Bool, +em: Bool) -> U32:
  match rd ob rs em:
    case True{} _ _ _:
      1
    case False{} True{} _ _:
      2
    case False{} False{} True{} _:
      3
    case False{} False{} False{} True{}:
      4
    case False{} False{} False{} False{}:
      0

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{+flag, r2}:
          main.cmd(cmd.of(String.eq(flag, "read"), String.eq(flag, "objects"), String.eq(flag, "resolve"), String.eq(flag, "emit")), r2)
        case Nil{}:
          main.out(Out{False{}, usage()})
    case Nil{}:
      main.out(Out{False{}, usage()})

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
