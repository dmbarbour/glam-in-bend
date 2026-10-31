import Base
import ./kprim.bend as P
import ./net.bend as N

# The kernel's rewrites, generated from the rule table (spike/rules.bend)
# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if
# this file differs from what the generator writes. One family, generic
# over what a strategy threads beside the net (knet.bend's Families): a
# stack, on which each link a rewrite makes between two principal ports
# is noted, or nothing.

# ports by kind code (R.arity)
def kind_arity(+k: U32) -> U32:
  match k:
    case 0:
      0
    case 1:
      3
    case 2:
      3
    case 3:
      3
    case 4:
      3
    case 5:
      1
    case 6:
      1
    case 7:
      1
    case 8:
      1
    case 9:
      2
    case 10:
      2
    case 11:
      2
    case 12:
      2
    case 13:
      2
    case 14:
      2
    case 15:
      2
    case 16:
      1
    case _:
      0

# 1 where the principal port is negative (R.port_pol): a table, where a
# match whose arms are constructors would be a chain
def kind_neg.n(+k: U32) -> U32:
  match k:
    case 0:
      0
    case 1:
      0
    case 2:
      1
    case 3:
      1
    case 4:
      0
    case 5:
      0
    case 6:
      1
    case 7:
      0
    case 8:
      1
    case 9:
      1
    case 10:
      1
    case 11:
      0
    case 12:
      1
    case 13:
      1
    case 14:
      0
    case 15:
      0
    case 16:
      1
    case _:
      0

def kind_neg(+k: U32) -> Bool:
  U32.is_eq(kind_neg.n(k), 1)

# the level checks the rewrites below make, for the kernel's interpreter
def check(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H:
  match ka kb:
    case 2 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 3 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 3 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 10 1:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 4:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 11:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 10 14:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 15:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 12 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 12 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 13 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 13 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case _ _:
      h

# the most active pairs one rewrite makes (R.pairs_made, over the table):
# a strategy's stack keeps room for that many before each rewrite (P.pop)
def most_pairs() -> U32:
  4

# a kind's class, its row and column in the rule table: each base kind
# its own, every code from the first operator's up one class, the
# operators', whose rule picks the operation by the code inside its step
# (header-kind-byte): a compare, where a table cost 2.3%; U32.is_lt, a
# native comparison, where Base's U32.min splits the word into its bits
def class.lt(lt: Bool, +k: U32) -> U32:
  match lt:
    case True{}:
      k
    case False{}:
      17

def class(+k: U32) -> U32:
  class.lt(U32.is_lt(k, 17), k)

# the rule's number for A, negative principal, of class ca meeting B of
# class cb, at ca times 18 plus cb: 0 for a pair no rule rewrites
def rule_at(+i: U32) -> U32:
  match i:
    case 0:
      0
    case 1:
      0
    case 2:
      0
    case 3:
      0
    case 4:
      0
    case 5:
      0
    case 6:
      0
    case 7:
      0
    case 8:
      0
    case 9:
      0
    case 10:
      0
    case 11:
      0
    case 12:
      0
    case 13:
      0
    case 14:
      0
    case 15:
      0
    case 16:
      0
    case 17:
      0
    case 18:
      0
    case 19:
      0
    case 20:
      0
    case 21:
      0
    case 22:
      0
    case 23:
      0
    case 24:
      0
    case 25:
      0
    case 26:
      0
    case 27:
      0
    case 28:
      0
    case 29:
      0
    case 30:
      0
    case 31:
      0
    case 32:
      0
    case 33:
      0
    case 34:
      0
    case 35:
      0
    case 36:
      0
    case 37:
      1
    case 38:
      0
    case 39:
      0
    case 40:
      2
    case 41:
      3
    case 42:
      0
    case 43:
      4
    case 44:
      0
    case 45:
      0
    case 46:
      0
    case 47:
      5
    case 48:
      0
    case 49:
      0
    case 50:
      6
    case 51:
      7
    case 52:
      0
    case 53:
      0
    case 54:
      0
    case 55:
      8
    case 56:
      0
    case 57:
      0
    case 58:
      9
    case 59:
      10
    case 60:
      0
    case 61:
      11
    case 62:
      0
    case 63:
      0
    case 64:
      0
    case 65:
      12
    case 66:
      0
    case 67:
      0
    case 68:
      13
    case 69:
      14
    case 70:
      0
    case 71:
      0
    case 72:
      0
    case 73:
      0
    case 74:
      0
    case 75:
      0
    case 76:
      0
    case 77:
      0
    case 78:
      0
    case 79:
      0
    case 80:
      0
    case 81:
      0
    case 82:
      0
    case 83:
      0
    case 84:
      0
    case 85:
      0
    case 86:
      0
    case 87:
      0
    case 88:
      0
    case 89:
      0
    case 90:
      0
    case 91:
      0
    case 92:
      0
    case 93:
      0
    case 94:
      0
    case 95:
      0
    case 96:
      0
    case 97:
      0
    case 98:
      0
    case 99:
      0
    case 100:
      0
    case 101:
      0
    case 102:
      0
    case 103:
      0
    case 104:
      0
    case 105:
      0
    case 106:
      0
    case 107:
      0
    case 108:
      0
    case 109:
      15
    case 110:
      0
    case 111:
      0
    case 112:
      16
    case 113:
      17
    case 114:
      0
    case 115:
      18
    case 116:
      0
    case 117:
      0
    case 118:
      0
    case 119:
      19
    case 120:
      0
    case 121:
      0
    case 122:
      20
    case 123:
      21
    case 124:
      0
    case 125:
      0
    case 126:
      0
    case 127:
      0
    case 128:
      0
    case 129:
      0
    case 130:
      0
    case 131:
      0
    case 132:
      0
    case 133:
      0
    case 134:
      0
    case 135:
      0
    case 136:
      0
    case 137:
      0
    case 138:
      0
    case 139:
      0
    case 140:
      0
    case 141:
      0
    case 142:
      0
    case 143:
      0
    case 144:
      0
    case 145:
      0
    case 146:
      0
    case 147:
      0
    case 148:
      0
    case 149:
      0
    case 150:
      0
    case 151:
      0
    case 152:
      0
    case 153:
      0
    case 154:
      0
    case 155:
      22
    case 156:
      0
    case 157:
      0
    case 158:
      0
    case 159:
      0
    case 160:
      0
    case 161:
      0
    case 162:
      0
    case 163:
      0
    case 164:
      0
    case 165:
      0
    case 166:
      52
    case 167:
      53
    case 168:
      0
    case 169:
      23
    case 170:
      0
    case 171:
      0
    case 172:
      0
    case 173:
      54
    case 174:
      0
    case 175:
      0
    case 176:
      24
    case 177:
      25
    case 178:
      0
    case 179:
      0
    case 180:
      0
    case 181:
      26
    case 182:
      0
    case 183:
      0
    case 184:
      27
    case 185:
      28
    case 186:
      0
    case 187:
      29
    case 188:
      0
    case 189:
      0
    case 190:
      0
    case 191:
      55
    case 192:
      0
    case 193:
      0
    case 194:
      30
    case 195:
      31
    case 196:
      0
    case 197:
      0
    case 198:
      0
    case 199:
      0
    case 200:
      0
    case 201:
      0
    case 202:
      0
    case 203:
      0
    case 204:
      0
    case 205:
      0
    case 206:
      0
    case 207:
      0
    case 208:
      0
    case 209:
      0
    case 210:
      0
    case 211:
      0
    case 212:
      0
    case 213:
      0
    case 214:
      0
    case 215:
      0
    case 216:
      0
    case 217:
      32
    case 218:
      0
    case 219:
      0
    case 220:
      33
    case 221:
      34
    case 222:
      0
    case 223:
      35
    case 224:
      0
    case 225:
      0
    case 226:
      0
    case 227:
      36
    case 228:
      0
    case 229:
      0
    case 230:
      37
    case 231:
      38
    case 232:
      0
    case 233:
      0
    case 234:
      0
    case 235:
      39
    case 236:
      0
    case 237:
      0
    case 238:
      40
    case 239:
      41
    case 240:
      0
    case 241:
      42
    case 242:
      0
    case 243:
      0
    case 244:
      0
    case 245:
      43
    case 246:
      0
    case 247:
      0
    case 248:
      44
    case 249:
      45
    case 250:
      0
    case 251:
      0
    case 252:
      0
    case 253:
      0
    case 254:
      0
    case 255:
      0
    case 256:
      0
    case 257:
      0
    case 258:
      0
    case 259:
      0
    case 260:
      0
    case 261:
      0
    case 262:
      0
    case 263:
      0
    case 264:
      0
    case 265:
      0
    case 266:
      0
    case 267:
      0
    case 268:
      0
    case 269:
      0
    case 270:
      0
    case 271:
      0
    case 272:
      0
    case 273:
      0
    case 274:
      0
    case 275:
      0
    case 276:
      0
    case 277:
      0
    case 278:
      0
    case 279:
      0
    case 280:
      0
    case 281:
      0
    case 282:
      0
    case 283:
      0
    case 284:
      0
    case 285:
      0
    case 286:
      0
    case 287:
      0
    case 288:
      0
    case 289:
      0
    case 290:
      0
    case 291:
      0
    case 292:
      46
    case 293:
      47
    case 294:
      0
    case 295:
      48
    case 296:
      0
    case 297:
      0
    case 298:
      0
    case 299:
      49
    case 300:
      0
    case 301:
      0
    case 302:
      50
    case 303:
      51
    case 304:
      0
    case 305:
      0
    case 306:
      0
    case 307:
      0
    case 308:
      0
    case 309:
      0
    case 310:
      0
    case 311:
      0
    case 312:
      0
    case 313:
      0
    case 314:
      0
    case 315:
      0
    case 316:
      0
    case 317:
      0
    case 318:
      0
    case 319:
      0
    case 320:
      0
    case 321:
      0
    case 322:
      0
    case 323:
      0
    case _:
      0

def rule_no(+ka: U32, +kb: U32) -> U32:
  rule_at(((class(ka) * 18 : U32) + class(kb) : U32))

# which payload test a rule's variants take: 0 none, 1 the levels' or the
# fans' sites, 2 whether B's data is a builtin function
def test_by(+r: U32) -> U32:
  match r:
    case 0:
      0
    case 1:
      1
    case 2:
      0
    case 3:
      2
    case 4:
      0
    case 5:
      0
    case 6:
      0
    case 7:
      0
    case 8:
      0
    case 9:
      1
    case 10:
      0
    case 11:
      0
    case 12:
      0
    case 13:
      1
    case 14:
      1
    case 15:
      0
    case 16:
      0
    case 17:
      0
    case 18:
      0
    case 19:
      0
    case 20:
      0
    case 21:
      0
    case 22:
      0
    case 23:
      0
    case 24:
      0
    case 25:
      0
    case 26:
      0
    case 27:
      0
    case 28:
      0
    case 29:
      0
    case 30:
      0
    case 31:
      0
    case 32:
      0
    case 33:
      1
    case 34:
      0
    case 35:
      0
    case 36:
      0
    case 37:
      1
    case 38:
      1
    case 39:
      0
    case 40:
      1
    case 41:
      0
    case 42:
      0
    case 43:
      0
    case 44:
      1
    case 45:
      1
    case 46:
      0
    case 47:
      0
    case 48:
      0
    case 49:
      0
    case 50:
      0
    case 51:
      0
    case 52:
      0
    case 53:
      0
    case 54:
      0
    case 55:
      0
    case _:
      0

# the payload test that picks a rule's variant where the two differ (R.rule's
# t; net.bend's rule_test), a template over the family and what follows
# the rewrite, for a copy in each strategy's chain: shared, it has two
# callers, and the compiler folds it into neither, which cost the eager
# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested
# after peeling instead (P.peel_ctl).
def test.k(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +k: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match k:
    case 1:
      (h, P.same_lvl(ha, hb))
    case 2:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case _:
      (h, False{})

def test(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +r: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(~S, ~R, ~note, ~fin, ~after, test_by(r), h, ha, hb, pa, pb)

# when the rule leaves A, negative principal, meeting B as it is (R.rule):
# 0 never, 1 always, 2 when the payload test fails, 3 when it passes; by
# the pair's rule (rule_no), a table, a pair no rule rewrites always
def stuck_of(+r: U32) -> U32:
  match r:
    case 0:
      1
    case 1:
      2
    case 2:
      0
    case 3:
      2
    case 4:
      0
    case 5:
      0
    case 6:
      0
    case 7:
      0
    case 8:
      0
    case 9:
      0
    case 10:
      0
    case 11:
      0
    case 12:
      0
    case 13:
      0
    case 14:
      0
    case 15:
      0
    case 16:
      0
    case 17:
      0
    case 18:
      0
    case 19:
      0
    case 20:
      0
    case 21:
      0
    case 22:
      0
    case 23:
      0
    case 24:
      0
    case 25:
      0
    case 26:
      0
    case 27:
      0
    case 28:
      0
    case 29:
      0
    case 30:
      0
    case 31:
      0
    case 32:
      0
    case 33:
      0
    case 34:
      0
    case 35:
      0
    case 36:
      0
    case 37:
      0
    case 38:
      0
    case 39:
      0
    case 40:
      0
    case 41:
      0
    case 42:
      0
    case 43:
      0
    case 44:
      0
    case 45:
      0
    case 46:
      0
    case 47:
      0
    case 48:
      0
    case 49:
      0
    case 50:
      0
    case 51:
      0
    case 52:
      0
    case 53:
      0
    case 54:
      0
    case 55:
      0
    case _:
      1

def stuck_by(+ka: U32, +kb: U32) -> U32:
  stuck_of(rule_no(ka, kb))

# does A, negative principal, meeting B make more nodes than the two it
# frees? (R.rule; the pairs a two-stack strategy defers) By the pair's
# rule, a table: 0 never, 1 always, 2 when the fans' levels agree, 3 when
# they do not
def grow_of(+r: U32) -> U32:
  match r:
    case 0:
      0
    case 1:
      0
    case 2:
      1
    case 3:
      0
    case 4:
      0
    case 5:
      1
    case 6:
      1
    case 7:
      1
    case 8:
      1
    case 9:
      3
    case 10:
      0
    case 11:
      0
    case 12:
      1
    case 13:
      3
    case 14:
      3
    case 15:
      0
    case 16:
      0
    case 17:
      0
    case 18:
      0
    case 19:
      0
    case 20:
      0
    case 21:
      0
    case 22:
      0
    case 23:
      0
    case 24:
      0
    case 25:
      0
    case 26:
      1
    case 27:
      1
    case 28:
      0
    case 29:
      0
    case 30:
      0
    case 31:
      0
    case 32:
      1
    case 33:
      3
    case 34:
      0
    case 35:
      0
    case 36:
      0
    case 37:
      0
    case 38:
      0
    case 39:
      1
    case 40:
      3
    case 41:
      0
    case 42:
      0
    case 43:
      0
    case 44:
      0
    case 45:
      0
    case 46:
      0
    case 47:
      0
    case 48:
      0
    case 49:
      0
    case 50:
      0
    case 51:
      0
    case 52:
      1
    case 53:
      0
    case 54:
      0
    case 55:
      0
    case _:
      0

def grows.k(+k: U32, +ha: U32, +hb: U32) -> Bool:
  match k:
    case 1:
      True{}
    case 2:
      P.same_lvl(ha, hb)
    case 3:
      Bool.not(P.same_lvl(ha, hb))
    case _:
      False{}

def grows(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:
  grows.k(grow_of(rule_no(ka, kb)), ha, hb)

def rw.Ap.Fn.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1), note(note(st, e0, e3), e1, e2)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.Merge.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e2), n1, e3), n2, e0), n3, e1))

def rw.Ap.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Ap.Merge.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1), note(st, n0, e0)), N.Ext4{P.nil(), e1, P.nil(), P.nil()})

def rw.Ap.Data.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.Data.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(9, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.EraP.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.LiftC.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeL.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.MergeL.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeR.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.MergeR.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e0), n1, e1), e2, n2), e3, n3))

def rw.Copy.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Copy.Fn.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1), note(note(st, e0, e2), e1, e3)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.Merge.no.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e0), n1, e1), n2, e2), n3, e3))

def rw.Copy.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Copy.Merge.no.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1))

def rw.Copy.Data.k2.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +dw) = r
  rw.Copy.Data.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(5, P.form(hb), P.fld(hb)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Data.k2.pre(~S, ~R, ~note, ~fin, ~after, P.dup(h, P.form(hb), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.EraP.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Copy.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.LiftC.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, e2), e1, n0), e0), note(note(st, e0, e2), e1, n0)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeL.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e0), n1, e1), n2, e2))

def rw.Copy.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.MergeL.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, n0), e1, e2), e1), note(note(st, e0, n0), e1, e2)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeR.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e0), n1, e1), n2, e2))

def rw.Copy.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.MergeR.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), n1, e3), note(note(st, n0, e2), n1, e3)), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.EraN.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), n1, e3), note(note(st, n0, e2), n1, e3)), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.EraN.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.drop(P.fresh2(h, a, b), P.form(hb), pb), st)

def rw.EraN.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.fresh2(h, a, b), st)

def rw.EraN.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e2), note(st, n0, e2))

def rw.Root.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Root.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(8, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e2), n1, e3), n2, e0))

def rw.Call.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Call.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.k2.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +dw) = r
  rw.Call.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(9, P.form(ha), P.fld(ha)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.Merge.k2.pre(~S, ~R, ~note, ~fin, ~after, P.dup(h, P.form(ha), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.Call.Data.k1.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & P.PW, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, pw) = r
  rw.Call.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode_pw(h, a, 5, pw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Data.k1.pre(~S, ~R, ~note, ~fin, ~after, P.apply(P.free(h, b), ha, pa, hb, pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Call.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.drop(P.free(h, b), P.form(ha), pa), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.Call.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e2), n1, e0))

def rw.Call.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e2), n1, e0))

def rw.Call.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.Lift.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Lift.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.Lift.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Lift.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.Lift.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.LiftC.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0), note(note(st, n0, e2), n1, e0))

def rw.Lift.LiftC.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.LiftC.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.LiftC.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.Pl, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> R:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), note(note(st, n0, e0), n1, e2))

def rw.Lift.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), note(note(st, n0, e0), n1, e2))

def rw.Lift.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), e2, n1), e3, n2))

def rw.CopyL.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyL.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, e2), n0, e3), e0), note(note(st, e0, e2), n0, e3)), N.Ext4{e0, P.nil(), P.nil(), e3})

def rw.CopyL.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Merge.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.CopyL.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyL.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.CopyL.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.CopyL.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(12, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyL.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.yes.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, e0, n1), n0, e2), note(note(st, e0, n1), n0, e2)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyL.MergeR.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeR.yes.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeR.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyL.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), e2, n1), e3, n2))

def rw.CopyR.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyR.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, n0, e2), e0, e3), e0), note(note(st, n0, e2), e0, e3)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Merge.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.CopyR.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyR.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.CopyR.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.CopyR.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(13, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.yes.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), e0, n1), note(note(st, n0, e2), e0, n1)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.MergeL.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeL.yes.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeL.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyR.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyR.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.DCall.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(h, n0, e2), n1, e3), note(note(st, n0, e2), n1, e3))

def rw.DCall.Merge.k2.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +dw) = r
  rw.DCall.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(16, P.form(ha), P.fld(ha)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.DCall.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.DCall.Merge.k2.pre(~S, ~R, ~note, ~fin, ~after, P.dup(h, P.form(ha), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.DCall.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(16, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.DCall.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.drop(P.drop(P.fresh2(h, a, b), P.form(ha), pa), P.form(hb), pb), st)

def rw.DCall.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.drop(P.fresh2(h, a, b), P.form(ha), pa), st)

def rw.DCall.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e2), note(st, n0, e2))

def rw.DCall.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(16, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.DCall.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e2), note(st, n0, e2))

def rw.DCall.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(16, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.DCall.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e2), note(st, n0, e2))

def rw.DCall.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(16, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# Events (R.event)

# rules linking two of their own new nodes into an event: none, or this
# names what does not exist
def inner_events() -> U32:
  0

# the eraser kind making an event at port p of kind k, 0 for none: two
# bits a port (0 none, 1 EraN, 2 EraP), eight a kind, four kinds a word
def ev_word(+w: U32) -> U32:
  match w:
    case 0:
      335544320
    case 1:
      40
    case 2:
      134480896
    case _:
      134743044

def ev_by.c(+c: U32) -> U32:
  match c:
    case 0:
      0
    case _:
      (c + 5 : U32)

def ev_by(+k: U32, +p: U32) -> U32:
  ev_by.c(((ev_word((k >> 2n : U32)) >> U32.to_nat((((k .&. 3 : U32) * 8 : U32) + (p * 2 : U32) : U32)) : U32) .&. 3 : U32))

# may port p of kind k be one end of an event: an eraser's principal, or
# an auxiliary port some eraser makes an event at
def ev_end(+k: U32, +p: U32) -> Bool:
  (U32.is_eq(p, 0) && U32.is_eq((k .|. 1 : U32), 7)) || U32.is_ne(ev_by(k, p), 0)

# the most active pairs one event makes
def ev_most() -> U32:
  0

def ev.Copy.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Copy.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Copy.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Copy.p2.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Copy.p2(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Copy.p2.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Merge.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Merge.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p2.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Merge.p2(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Merge.p2.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Call.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.Call.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Call.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(16, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Lift.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.Lift.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Lift.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.LiftC.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.LiftC.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.LiftC.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyL.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.CopyL.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.CopyL.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyR.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.CopyR.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.CopyR.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeL.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.MergeL.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.MergeL.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeR.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.MergeR.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.MergeR.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# the event at port p of a node of kind ka, A, the eraser facing it B;
# e0 the peer of A's principal, e1 of its other auxiliary port; the net
# and the family's state, the pairs it makes noted
def event(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, +ka: U32, +p: U32, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  match ka p:
    case 3 1:
      ev.Copy.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 2:
      ev.Copy.p2(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 1:
      ev.Merge.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 2:
      ev.Merge.p2(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 1:
      ev.Call.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      ev.Lift.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 11 1:
      ev.LiftC.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      ev.CopyL.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      ev.CopyR.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 14 1:
      ev.MergeL.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 15 1:
      ev.MergeR.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      (P.h_err(h), st)

# the stuck pairs' arm, and each rule's
def rw.arm.r0(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.err_if(U32.is_ne(ka, 8), h), st)

def rw.arm.r1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.Ap.Fn.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      fin(P.err_if(U32.is_ne(ka, 8), h), st)

def rw.arm.r2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.Ap.Data.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      fin(P.err_if(U32.is_ne(ka, 8), h), st)

def rw.arm.r4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r5(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r6(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r7(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r8(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r9(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.Copy.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.Copy.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r10(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r11(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r12(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r13(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.Copy.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.Copy.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r14(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.Copy.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.Copy.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r15(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Fn(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r16(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r17(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r18(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r19(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r20(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r21(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r22(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Root.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r23(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r24(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r25(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r27(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Merge(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r28(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r29(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r30(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeL(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r31(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeR(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r32(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r33(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyL.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyL.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r34(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r35(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r36(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r37(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyL.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyL.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r38(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyL.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyL.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r39(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r40(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyR.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyR.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r41(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r42(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r43(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r44(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyR.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyR.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r45(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match t:
    case True{}:
      rw.CopyR.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.CopyR.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r46(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r47(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r48(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r49(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r50(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r51(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.DCall.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r53(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r54(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.arm.r55(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.LiftC.peeled(~S, ~R, ~note, ~fin, ~after, P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)

def rw.t.r50.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r50(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r51(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r50.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r50.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 51), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r48.r50.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r48(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r49(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r48.r50(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r48.r50.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 49), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r48.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r48.r50(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r50.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r48.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r48.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 50), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r46.r48.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r46(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r47(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r46.r48(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r46.r48.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 47), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r45.r48.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r45(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r46.r48(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r45.r48(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r45.r48.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 46), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r45.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r45.r48(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r48.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r45.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r45.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 48), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r43.r45.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r43(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r44(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r43.r45(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r43.r45.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 44), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r42.r45.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r42(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r43.r45(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r42.r45(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r42.r45.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 43), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r40.r42.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r40(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r41(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r40.r42(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r40.r42.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 41), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r42.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r39(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r40.r42(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r42(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r39.r42.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 40), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r45.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r39.r42(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r42.r45(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r45(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r39.r45.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 42), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r39.r45(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r45.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r39.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r39.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 45), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r37.r39.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r37(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r38(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r37.r39(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r37.r39.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 38), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r35.r37.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r35(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r36(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r35.r37(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r35.r37.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 36), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r35.r39.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r35.r37(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r37.r39(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r35.r39(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r35.r39.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 37), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r33.r35.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r33(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r34(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r33.r35(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r33.r35.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 34), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r32.r35.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r32(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r33.r35(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r32.r35(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r32.r35.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 33), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r32.r39.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r32.r35(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r35.r39(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r32.r39(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r32.r39.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 35), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r30.r32.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r30(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r31(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r30.r32(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r30.r32.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 31), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r29.r32.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r29(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r30.r32(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r29.r32(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r29.r32.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 30), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r27.r29.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r27(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r28(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r27.r29(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r27.r29.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 28), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r29.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r26(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r27.r29(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r29(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r26.r29.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 27), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r32.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r26.r29(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r29.r32(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r32(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r26.r32.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 29), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r39.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r26.r32(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r32.r39(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r39(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r26.r39.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 32), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r26.r39(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r39.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r26.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r26.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 39), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r24.r26.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r24(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r25(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r24.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r24.r26.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 25), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r22.r24.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r22(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r23(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r22.r24(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r22.r24.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 23), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r22.r26.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r22.r24(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r24.r26(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r22.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r22.r26.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 24), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r20.r22.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r20(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r21(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r20.r22(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r20.r22.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 21), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r19.r22.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r19(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r20.r22(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r19.r22(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r19.r22.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 20), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r19.r26.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r19.r22(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r22.r26(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r19.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r19.r26.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 22), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r17.r19.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r17(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r18(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r17.r19(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r17.r19.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 18), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r16.r19.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r16(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r17.r19(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r16.r19(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r16.r19.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 17), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r14.r16.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r14(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r15(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r14.r16(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r14.r16.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 15), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r16.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r13(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r14.r16(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r16(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r13.r16.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 14), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r19.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r13.r16(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r16.r19(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r19(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r13.r19.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 16), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r26.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r13.r19(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r19.r26(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r13.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r13.r26.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 19), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r11.r13.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r11(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r12(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r11.r13(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r11.r13.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 12), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r9.r11.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r9(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r10(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r9.r11(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r9.r11.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 10), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r9.r13.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r9.r11(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r11.r13(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r9.r13(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r9.r13.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 11), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r7.r9.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r7(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r8(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r7.r9(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r7.r9.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 8), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r6.r9.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r6(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r7.r9(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r6.r9(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r6.r9.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 7), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r6.r13.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r6.r9(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r9.r13(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r6.r13(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r6.r13.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 9), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r4.r6.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r4(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r5(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r4.r6(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r4.r6.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 5), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r3.r6.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r3(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r4.r6(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r3.r6(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r3.r6.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 4), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r1.r3.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r1(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.arm.r2(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r1.r3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r1.r3.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 2), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r3.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.arm.r0(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r1.r3(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r0.r3.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 1), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r6.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r0.r3(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r3.r6(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r6(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r0.r6.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 3), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r13.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r0.r6(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r6.r13(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r13(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r0.r13.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 6), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r26.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r0.r13(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r13.r26(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r26(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r0.r26.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 13), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r52.go(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, lt: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match lt:
    case True{}:
      rw.t.r0.r26(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r26.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.t.r0.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.t.r0.r52.go(~S, ~R, ~note, ~fin, ~after, U32.is_lt(r, 26), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.d.r55(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, hit: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match hit:
    case True{}:
      rw.arm.r55(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.t.r0.r52(~S, ~R, ~note, ~fin, ~after, ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.d.r54(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, hit: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match hit:
    case True{}:
      rw.arm.r54(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.d.r55(~S, ~R, ~note, ~fin, ~after, U32.is_eq(r, 55), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.d.r53(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, hit: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match hit:
    case True{}:
      rw.arm.r53(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.d.r54(~S, ~R, ~note, ~fin, ~after, U32.is_eq(r, 54), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.d.r52(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, hit: Bool, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match hit:
    case True{}:
      rw.arm.r52(~S, ~R, ~note, ~fin, ~after, ka, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case False{}:
      rw.d.r53(~S, ~R, ~note, ~fin, ~after, U32.is_eq(r, 53), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# the rewrite for A, negative principal, of kind ka, meeting B by rule r
# (rule_no); t is the payload test; then `after`, at the external peers
# where the rule may make an event
def rewrite(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +r: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.d.r52(~S, ~R, ~note, ~fin, ~after, U32.is_eq(r, 52), ka, r, t, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

