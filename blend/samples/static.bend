# Written by Blend from static.blend; do not edit.
import Base

# blend: static.blend:20
def Quiet.verbose() -> Bool:
  False{}

# blend: static.blend:12
def Quiet.note.go(+v: Bool, +n: U32, s: String) -> String:
  match v:
    case True{}:
      s ++ " #" ++ U32.show(n)
    case False{}:
      s

# blend: static.blend:10
def Quiet.note(+n: U32, s: String) -> String:
  Quiet.note.go(Quiet.verbose(), n, s)

# blend: static.blend:24
def Chatty.verbose() -> Bool:
  True{}

# blend: static.blend:12
def Chatty.note.go(+v: Bool, +n: U32, s: String) -> String:
  match v:
    case True{}:
      s ++ " #" ++ U32.show(n)
    case False{}:
      s

# blend: static.blend:10
def Chatty.note(+n: U32, s: String) -> String:
  Chatty.note.go(Chatty.verbose(), n, s)

# blend: static.blend:27
def main() -> IO(Unit):
  IO.print(Quiet.note(3, "done") ++ " / " ++ Chatty.note(3, "done"))
