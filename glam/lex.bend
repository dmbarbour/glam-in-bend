import Base

# The ".g" lexer, as far as the hello ladder has climbed (HelloLadder,
# ladder-text): a file's bytes to tokens, each with its line and column,
# since diagnostics name lines (samples/invalid's .expect files) and the
# layout reads columns (a declaration starts at column 0; its
# continuation lines are indented, docs/Syntax.md, Toplevel Structure).
# Comments, `#` to the end of the line, and blanks are dropped. Texts are
# raw: the bytes between two quotes, no escapes (Embedded Texts); a `"""`
# block is not lexed yet. A run of operator symbols is one operator, `++`,
# `:=`, `|>`, a lone `=` being the definition's sign; brackets, commas and
# semicolons are tokens of one byte. A byte past ASCII is kept where it stands, in a
# text or a comment, and the line of the first one is reported beside
# the tokens, so that the parser, knowing whether `with utf8` was
# declared, can refuse it (Character Set): the lexer does not know the
# header. Lines are counted at LF; CR before it is blank.
#
# One pass over the bytes, one byte a step, structural on the list so
# that it terminates without fuel (Bend admits no other recursion here),
# the state beside it: the position of the byte, the mode (in a word, a
# text, a comment, or between tokens) with the token begun, the tokens so
# far reversed, and the first non-ASCII line.

type Tok is Data:
  # a word: a name part, a keyword, a number's digits
  TWord{+line: U32, +col: U32, s: List<&2, U32>}
  TDot{+line: U32, +col: U32}
  TEq{+line: U32, +col: U32}
  # a text's bytes, the quotes left out
  TText{+line: U32, +col: U32, s: List<&2, U32>}
  # a text whose closing quote never came on its line
  TOpen{+line: U32, +col: U32}
  # a bracket, a comma or a semicolon: one of `[](){},;`
  TPun{+line: U32, +col: U32, +b: U32}
  # an operator: a run of operator symbols other than a lone `=`, and
  # whether it is joint to the token before it (no blank between)
  TOp{+line: U32, +col: U32, s: List<&2, U32>, +jl: Bool}
  # a binding group's layout made explicit (glam/layout.bend): 0 its
  # virtual open, 1 a separator, 2 its close
  TLay{+line: U32, +col: U32, +k: U32}
  # any other byte, for the parser to name
  TOther{+line: U32, +col: U32, +b: U32}

# the tokens, and the line of the first byte past ASCII, 0 for none
type Lx is Data:
  Lx{toks: List<&2, Tok>, +na: U32}

def tok_line(t: Tok) -> U32:
  match t:
    case TWord{+line, +col, s}:
      line
    case TDot{+line, +col}:
      line
    case TEq{+line, +col}:
      line
    case TText{+line, +col, s}:
      line
    case TOpen{+line, +col}:
      line
    case TOther{+line, +col, +b}:
      line
    case TPun{+line, +col, +b}:
      line
    case TOp{+line, +col, s, +jl}:
      line
    case TLay{+line, +col, +k}:
      line

def tok_col(t: Tok) -> U32:
  match t:
    case TWord{+line, +col, s}:
      col
    case TDot{+line, +col}:
      col
    case TEq{+line, +col}:
      col
    case TText{+line, +col, s}:
      col
    case TOpen{+line, +col}:
      col
    case TOther{+line, +col, +b}:
      col
    case TPun{+line, +col, +b}:
      col
    case TOp{+line, +col, s, +jl}:
      col
    case TLay{+line, +col, +k}:
      col

# two byte lists alike
def bytes_is(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Con{+x, xs} Con{+y, ys}:
      U32.is_eq(x, y) && bytes_is(xs, ys)
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def is_letter(+b: U32) -> Bool:
  (U32.is_ge(b, 97) && U32.is_le(b, 122)) || (U32.is_ge(b, 65) && U32.is_le(b, 90))

def is_digit(+b: U32) -> Bool:
  U32.is_ge(b, 48) && U32.is_lt(b, 58)

# a byte that continues a word: a letter, a digit, an underscore
def is_wordy(+b: U32) -> Bool:
  is_letter(b) || is_digit(b) || U32.is_eq(b, 95)

def na_pick(+none: Bool, +na: U32, +line: U32) -> U32:
  match none:
    case True{}:
      line
    case False{}:
      na

def na_first.k(+past: Bool, +na: U32, +line: U32) -> U32:
  match past:
    case True{}:
      na_pick(U32.is_eq(na, 0), na, line)
    case False{}:
      na

# the first non-ASCII line: the one noted already, else this one if b is
def na_first(+na: U32, +b: U32, +line: U32) -> U32:
  na_first.k(U32.is_ge(b, 128), na, line)

# a bracket, a comma or a semicolon
def is_pun(+b: U32) -> Bool:
  U32.is_eq(b, 91) || U32.is_eq(b, 93) || U32.is_eq(b, 40) || U32.is_eq(b, 41) ||
    U32.is_eq(b, 123) || U32.is_eq(b, 125) || U32.is_eq(b, 44) || U32.is_eq(b, 59)

# an operator symbol: one of `+-*/<>|!&=:^%~?@$\`
def is_sym(+b: U32) -> Bool:
  U32.is_eq(b, 43) || U32.is_eq(b, 45) || U32.is_eq(b, 42) || U32.is_eq(b, 47) ||
    U32.is_eq(b, 60) || U32.is_eq(b, 62) || U32.is_eq(b, 124) || U32.is_eq(b, 33) ||
    U32.is_eq(b, 38) || U32.is_eq(b, 61) || U32.is_eq(b, 58) || U32.is_eq(b, 94) ||
    U32.is_eq(b, 37) || U32.is_eq(b, 126) || U32.is_eq(b, 63) || U32.is_eq(b, 64) ||
    U32.is_eq(b, 36) || U32.is_eq(b, 92)

# the mode: 0 between tokens after a blank, 6 just after a token, 1 in a
# word begun at column `at`, 2 in a text opened at `at`, 3 in a comment,
# 4 in an operator begun at `at` joint to the token before, 5 one that is
# not
type St is Data:
  St{+line: U32, +col: U32, +mode: U32, +at: U32, acc: List<&2, U32>, toks: List<&2, Tok>, +na: U32}

def class.k(+blank: Bool, +nl: Bool, +hash: Bool, +wordy: Bool, +quote: Bool, +dot: Bool, +eq: Bool) -> U32:
  match blank nl hash wordy quote dot eq:
    case True{} _ _ _ _ _ _:
      0
    case False{} True{} _ _ _ _ _:
      1
    case False{} False{} True{} _ _ _ _:
      2
    case False{} False{} False{} True{} _ _ _:
      3
    case False{} False{} False{} False{} True{} _ _:
      4
    case False{} False{} False{} False{} False{} True{} _:
      5
    case False{} False{} False{} False{} False{} False{} True{}:
      6
    case False{} False{} False{} False{} False{} False{} False{}:
      7

def class.p(+k: U32, +pun: Bool, +sym: Bool) -> U32:
  match k pun sym:
    case 7 True{} _:
      8
    case 7 False{} True{}:
      9
    case _ _ _:
      k

# the byte's class: 0 blank, 1 newline, 2 comment, 3 a word's start, 4 a
# quote, 5 a dot, 6 (unused: `=` is an operator symbol), 7 anything else,
# 8 a bracket, a comma or a semicolon, 9 an operator symbol
def class(+b: U32) -> U32:
  class.p(class.k(U32.is_eq(b, 32) || U32.is_eq(b, 13), U32.is_eq(b, 10), U32.is_eq(b, 35), is_letter(b) || is_digit(b) || U32.is_eq(b, 95), U32.is_eq(b, 34), U32.is_eq(b, 46), False{}), is_pun(b), is_sym(b))

# an operator's mode from whether a blank came before it
def op_mode(+gap: Bool) -> U32:
  match gap:
    case True{}:
      5
    case False{}:
      4

# a byte between tokens, a blank before it or not
def plain.k(+k: U32, +gap: Bool, +b: U32, +line: U32, +col: U32, toks: List<&2, Tok>, +na: U32) -> St:
  match k:
    case 0:
      St{line, (col + 1 : U32), 0, 0, Nil{}, toks, na}
    case 1:
      St{(line + 1 : U32), 0, 0, 0, Nil{}, toks, na}
    case 2:
      St{line, (col + 1 : U32), 3, 0, Nil{}, toks, na}
    case 3:
      St{line, (col + 1 : U32), 1, col, [b], toks, na}
    case 4:
      St{line, (col + 1 : U32), 2, col, Nil{}, toks, na}
    case 5:
      St{line, (col + 1 : U32), 6, 0, Nil{}, Con{TDot{line, col}, toks}, na}
    case 8:
      St{line, (col + 1 : U32), 6, 0, Nil{}, Con{TPun{line, col, b}, toks}, na}
    case 9:
      St{line, (col + 1 : U32), op_mode(gap), col, [b], toks, na}
    case _:
      St{line, (col + 1 : U32), 6, 0, Nil{}, Con{TOther{line, col, b}, toks}, na_first(na, b, line)}

def plain(+gap: Bool, +b: U32, +line: U32, +col: U32, toks: List<&2, Tok>, +na: U32) -> St:
  plain.k(class(b), gap, b, line, col, toks, na)

# a byte in a word: more of it, or the word ends and b is read plain
def in_word(+more: Bool, +b: U32, +line: U32, +col: U32, +at: U32, acc: List<&2, U32>, toks: List<&2, Tok>, +na: U32) -> St:
  match more:
    case True{}:
      St{line, (col + 1 : U32), 1, at, Con{b, acc}, toks, na}
    case False{}:
      plain(False{}, b, line, col, Con{TWord{line, at, List.reverse(&2, U32, acc)}, toks}, na)

# an operator ended: a lone `=` is the definition's sign, any other run
# an operator
def op_tok.k(+eq: Bool, +line: U32, +at: U32, s: List<&2, U32>, +jl: Bool) -> Tok:
  match eq:
    case True{}:
      TEq{line, at}
    case False{}:
      TOp{line, at, s, jl}

def op_tok(+line: U32, +at: U32, s: List<&2, U32>, +jl: Bool) -> Tok:
  match s:
    case Con{+b, +rest}:
      op_tok.k(U32.is_eq(b, 61) && List.is_empty(&2, U32, rest), line, at, Con{b, rest}, jl)
    case Nil{}:
      TOp{line, at, Nil{}, jl}

# a byte in an operator: more of it, or the operator ends and b is read
# plain
def in_op(+more: Bool, +jl: Bool, +b: U32, +line: U32, +col: U32, +at: U32, acc: List<&2, U32>, toks: List<&2, Tok>, +na: U32) -> St:
  match more:
    case True{}:
      St{line, (col + 1 : U32), op_mode(Bool.not(jl)), at, Con{b, acc}, toks, na}
    case False{}:
      plain(False{}, b, line, col, Con{op_tok(line, at, List.reverse(&2, U32, acc), jl), toks}, na)

# a byte in a text: its close, a line's end leaving it open, or more of it
def in_text(+close: Bool, +nl: Bool, +b: U32, +line: U32, +col: U32, +at: U32, acc: List<&2, U32>, toks: List<&2, Tok>, +na: U32) -> St:
  match close nl:
    case True{} _:
      St{line, (col + 1 : U32), 6, 0, Nil{}, Con{TText{line, at, List.reverse(&2, U32, acc)}, toks}, na}
    case False{} True{}:
      plain(False{}, b, line, col, Con{TOpen{line, at}, toks}, na)
    case False{} False{}:
      St{line, (col + 1 : U32), 2, at, Con{b, acc}, toks, na_first(na, b, line)}

# a byte in a comment: the line's end, read plain, or more of it
def in_comment(+nl: Bool, +b: U32, +line: U32, +col: U32, toks: List<&2, Tok>, +na: U32) -> St:
  match nl:
    case True{}:
      plain(True{}, b, line, col, toks, na)
    case False{}:
      St{line, (col + 1 : U32), 3, 0, Nil{}, toks, na_first(na, b, line)}

def byte(st: St, +b: U32) -> St:
  match st:
    case St{+line, +col, +mode, +at, acc, toks, +na}:
      match mode:
        case 0:
          plain(True{}, b, line, col, toks, na)
        case 6:
          plain(False{}, b, line, col, toks, na)
        case 1:
          in_word(is_wordy(b), b, line, col, at, acc, toks, na)
        case 2:
          in_text(U32.is_eq(b, 34), U32.is_eq(b, 10), b, line, col, at, acc, toks, na)
        case 3:
          in_comment(U32.is_eq(b, 10), b, line, col, toks, na)
        case 4:
          in_op(is_sym(b), True{}, b, line, col, at, acc, toks, na)
        case _:
          in_op(is_sym(b), False{}, b, line, col, at, acc, toks, na)

# the end of the bytes: a word or a text begun is ended
def finish(st: St) -> Lx:
  match st:
    case St{+line, +col, +mode, +at, acc, toks, +na}:
      match mode:
        case 1:
          Lx{List.reverse(&2, Tok, Con{TWord{line, at, List.reverse(&2, U32, acc)}, toks}), na}
        case 2:
          Lx{List.reverse(&2, Tok, Con{TOpen{line, at}, toks}), na}
        case 4:
          Lx{List.reverse(&2, Tok, Con{op_tok(line, at, List.reverse(&2, U32, acc), True{}), toks}), na}
        case 5:
          Lx{List.reverse(&2, Tok, Con{op_tok(line, at, List.reverse(&2, U32, acc), False{}), toks}), na}
        case _:
          Lx{List.reverse(&2, Tok, toks), na}

def scan(bs: List<&2, U32>, st: St) -> Lx:
  match bs:
    case Con{+b, rest}:
      scan(rest, byte(st, b))
    case Nil{}:
      finish(st)

# a file's bytes to its tokens, lines from 1 and columns from 0
def lex(bs: List<&2, U32>) -> Lx:
  scan(bs, St{1, 0, 0, 0, Nil{}, Nil{}, 0})
