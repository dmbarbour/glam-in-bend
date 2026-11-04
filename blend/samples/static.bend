# Written by Blend from static.blend; do not edit.
import Base

def Quiet.verbose() -> Bool:
  False{}

def Quiet.note.go(+v: Bool, +n: U32, s: String) -> String:
  match v:
    case True{}:
      s ++ " #" ++ U32.show(n)
    case False{}:
      s

def Quiet.note(+n: U32, s: String) -> String:
  Quiet.note.go(Quiet.verbose(), n, s)

def Chatty.verbose() -> Bool:
  True{}

def Chatty.note.go(+v: Bool, +n: U32, s: String) -> String:
  match v:
    case True{}:
      s ++ " #" ++ U32.show(n)
    case False{}:
      s

def Chatty.note(+n: U32, s: String) -> String:
  Chatty.note.go(Chatty.verbose(), n, s)

def main() -> IO(Unit):
  IO.print(Quiet.note(3, "done") ++ " / " ++ Chatty.note(3, "done"))
