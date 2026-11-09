import Base
import ./lex.bend as L

# Layout (HelloLadder, ladder-locals): a declaration's tokens with the
# binding groups of `let` and `where` made explicit, as Haskell's layout
# algorithm makes them (docs/Syntax.md, Layout Bodies and Expression
# Resumption; Local Definitions). After `let` or `where`, unless a `{`
# follows, the next token's column anchors an implicit group: a virtual
# open is put before it, a virtual separator before each later line that
# begins at the anchor, and a virtual close before the first line that
# begins left of it. `in` closes an implicit `let` group on its line;
# a comma or a closing bracket closes the implicit groups opened inside
# its bracket; the declaration's end closes every group still open.
# Brackets are explicit: no virtual token is put inside one opened after
# the group (Toplevel Structure: groups are hard expression boundaries).
# Naked semicolons stay as they are, for the parser to refuse in an
# implicit group (Local Definitions).
#
# Bend admits no mutual recursion: a loop's decision on its head goes to
# a helper above it, given the loop's next call as a thunk (Base's
# List.any.if).

# a context: 0 a bracket, 3 an explicit group's `{`, or an implicit
# group, 1 `let`'s or 2 `where`'s, anchored at a column
type Cx is Data:
  Cx{+kind: U32, +col: U32}

# the contexts open, the group a keyword left pending (0 none, 1 `let`,
# 2 `where`), the last token's line, the tokens so far reversed
type Ls is Data:
  Ls{ctx: List<&2, Cx>, +pend: U32, +last: U32, out: List<&2, L.Tok>}

def vopen(+line: U32, +col: U32) -> L.Tok:
  L.TLay{line, col, 0}

def vsep(+line: U32, +col: U32) -> L.Tok:
  L.TLay{line, col, 1}

def vclose(+line: U32, +col: U32) -> L.Tok:
  L.TLay{line, col, 2}

def is_implicit(+k: U32) -> Bool:
  U32.is_eq(k, 1) || U32.is_eq(k, 2)

# the contexts and the tokens so far
type Cs is Data:
  Cs{ctx: List<&2, Cx>, out: List<&2, L.Tok>}

def dedent.if(more: Unit -> Cs, +close: Bool, +sep: Bool, +k: U32, +a: U32, rest: List<&2, Cx>, +line: U32, +col: U32, out: List<&2, L.Tok>) -> Cs:
  match close sep:
    case True{} _:
      more(Unit{})
    case False{} True{}:
      Cs{Con{Cx{k, a}, rest}, Con{vsep(line, col), out}}
    case False{} False{}:
      Cs{Con{Cx{k, a}, rest}, out}

# a line beginning at col: the implicit groups anchored right of it
# closed, then a separator if it begins at the anchor of the one left
def dedent(ctx: List<&2, Cx>, +line: U32, +col: U32, +out: List<&2, L.Tok>) -> Cs:
  match ctx:
    case Nil{}:
      Cs{Nil{}, out}
    case Con{c, +rest}:
      match c:
        case Cx{+k, +a}:
          dedent.if(u => dedent(rest, line, col, Con{vclose(line, col), out}), is_implicit(k) && U32.is_gt(a, col), is_implicit(k) && U32.is_eq(a, col), k, a, rest, line, col, out)

def close.if(more: Unit -> Cs, +imp: Bool, +k: U32, +a: U32, rest: List<&2, Cx>, out: List<&2, L.Tok>) -> Cs:
  match imp:
    case True{}:
      more(Unit{})
    case False{}:
      Cs{Con{Cx{k, a}, rest}, out}

# the implicit groups on top closed, down to a bracket or the bottom
def close_implicit(ctx: List<&2, Cx>, +line: U32, +col: U32, +out: List<&2, L.Tok>) -> Cs:
  match ctx:
    case Nil{}:
      Cs{Nil{}, out}
    case Con{c, +rest}:
      match c:
        case Cx{+k, +a}:
          close.if(u => close_implicit(rest, line, col, Con{vclose(line, col), out}), is_implicit(k), k, a, rest, out)

# Tokens
# ======

def word_part.k(+is_in: Bool, +is_let: Bool, +is_where: Bool) -> U32:
  match is_in is_let is_where:
    case True{} _ _:
      1
    case False{} True{} _:
      2
    case False{} False{} True{}:
      3
    case False{} False{} False{}:
      0

# a token's part in layout: 1 `in`, 2 `let`, 3 `where`, 4 an opening
# bracket, 5 a closing one, 6 a comma, 0 anything else
def word_part(+s: List<&2, U32>) -> U32:
  word_part.k(L.bytes_is(s, [105, 110]), L.bytes_is(s, [108, 101, 116]), L.bytes_is(s, [119, 104, 101, 114, 101]))

def pun_part(+b: U32) -> U32:
  match b:
    case 40:
      4
    case 91:
      4
    case 123:
      4
    case 41:
      5
    case 93:
      5
    case 125:
      5
    case 44:
      6
    case _:
      0

def part(t: L.Tok) -> U32:
  match t:
    case L.TWord{+l, +c, s}:
      word_part(s)
    case L.TPun{+l, +c, +b}:
      pun_part(b)
    case _:
      0

# the keyword `in`
def is_in(t: L.Tok) -> Bool:
  U32.is_eq(part(t), 1)

def is_brace(t: L.Tok) -> Bool:
  match t:
    case L.TPun{+l, +c, +b}:
      U32.is_eq(b, 123)
    case _:
      False{}

def pop.k(+br: Bool, +k: U32, +a: U32, rest: List<&2, Cx>) -> List<&2, Cx>:
  match br:
    case True{}:
      rest
    case False{}:
      Con{Cx{k, a}, rest}

# a closing bracket's context popped, where it is the bracket's
def pop_bracket(ctx: List<&2, Cx>) -> List<&2, Cx>:
  match ctx:
    case Nil{}:
      Nil{}
    case Con{c, rest}:
      match c:
        case Cx{+k, +a}:
          pop.k(Bool.not(is_implicit(k)), k, a, rest)

def in.k(+is_let: Bool, +k: U32, +a: U32, rest: List<&2, Cx>, +line: U32, +col: U32, out: List<&2, L.Tok>) -> Cs:
  match is_let:
    case True{}:
      Cs{rest, Con{vclose(line, col), out}}
    case False{}:
      Cs{Con{Cx{k, a}, rest}, out}

# `in`: an implicit `let` group on top closed
def in_close(ctx: List<&2, Cx>, +line: U32, +col: U32, out: List<&2, L.Tok>) -> Cs:
  match ctx:
    case Nil{}:
      Cs{Nil{}, out}
    case Con{c, rest}:
      match c:
        case Cx{+k, +a}:
          in.k(U32.is_eq(k, 1), k, a, rest, line, col, out)

def emit(r: Cs, +pend: U32, +t: L.Tok) -> Ls:
  match r:
    case Cs{ctx, out}:
      Ls{ctx, pend, L.tok_line(t), Con{t, out}}

def closed(r: Cs, +pop: Bool, +t: L.Tok) -> Ls:
  match r:
    case Cs{ctx, out}:
      match pop:
        case True{}:
          Ls{pop_bracket(ctx), 0, L.tok_line(t), Con{t, out}}
        case False{}:
          Ls{ctx, 0, L.tok_line(t), Con{t, out}}

# a token itself, its position's virtual tokens put already
def token.k(+p: U32, ctx: List<&2, Cx>, out: List<&2, L.Tok>, +t: L.Tok) -> Ls:
  match p:
    case 1:
      emit(in_close(ctx, L.tok_line(t), L.tok_col(t), out), 0, t)
    case 2:
      emit(Cs{ctx, out}, 1, t)
    case 3:
      emit(Cs{ctx, out}, 2, t)
    case 4:
      emit(Cs{Con{Cx{0, 0}, ctx}, out}, 0, t)
    case 5:
      closed(close_implicit(ctx, L.tok_line(t), L.tok_col(t), out), True{}, t)
    case 6:
      closed(close_implicit(ctx, L.tok_line(t), L.tok_col(t), out), False{}, t)
    case _:
      emit(Cs{ctx, out}, 0, t)

def token(r: Cs, +t: L.Tok) -> Ls:
  match r:
    case Cs{ctx, out}:
      token.k(part(t), ctx, out, t)

# a group's first token: a `{` makes it explicit, anything else anchors
# an implicit one at its column
def opened.k(+brace: Bool, +pend: U32, ctx: List<&2, Cx>, out: List<&2, L.Tok>, +t: L.Tok) -> Ls:
  match brace:
    case True{}:
      Ls{Con{Cx{3, 0}, ctx}, 0, L.tok_line(t), Con{t, out}}
    case False{}:
      token(Cs{Con{Cx{pend, L.tok_col(t)}, ctx}, Con{vopen(L.tok_line(t), L.tok_col(t)), out}}, t)

def normal.k(+first: Bool, ctx: List<&2, Cx>, out: List<&2, L.Tok>, +t: L.Tok) -> Ls:
  match first:
    case True{}:
      token(dedent(ctx, L.tok_line(t), L.tok_col(t), out), t)
    case False{}:
      token(Cs{ctx, out}, t)

def step(st: Ls, +t: L.Tok) -> Ls:
  match st:
    case Ls{ctx, +pend, +last, out}:
      match pend:
        case 0:
          normal.k(Bool.not(U32.is_eq(L.tok_line(t), last)), ctx, out, t)
        case _:
          opened.k(is_brace(t), pend, ctx, out, t)

def finish.k(+pend: U32, +last: U32, ctx: List<&2, Cx>, out: List<&2, L.Tok>) -> Cs:
  match pend:
    case 0:
      close_implicit(ctx, last, 0, out)
    case _:
      close_implicit(ctx, last, 0, Con{vclose(last, 0), Con{vopen(last, 0), out}})

def finish.r(r: Cs) -> List<&2, L.Tok>:
  match r:
    case Cs{c, o}:
      List.reverse(&2, L.Tok, o)

# the declaration's end: a pending group opened empty, every implicit
# group on top closed
def finish(st: Ls) -> List<&2, L.Tok>:
  match st:
    case Ls{ctx, +pend, +last, out}:
      finish.r(finish.k(pend, last, ctx, out))

def go(ts: List<&2, L.Tok>, st: Ls) -> List<&2, L.Tok>:
  match ts:
    case Nil{}:
      finish(st)
    case Con{+t, rest}:
      go(rest, step(st, t))

# a declaration's tokens, its binding groups made explicit
def layout(ts: List<&2, L.Tok>) -> List<&2, L.Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      go(Con{t, rest}, Ls{Nil{}, 0, L.tok_line(t), Nil{}})
