# Written by Blend from override.blend; do not edit.
import Base

def Greeter.greet() -> String:
  "hello"

def Greeter.show() -> String:
  Greeter.greet() ++ ", world"

def Loud.greet() -> String:
  "HELLO"

def Loud.show() -> String:
  Loud.greet() ++ ", world"

def main() -> IO(Unit):
  IO.print(Greeter.show() ++ " / " ++ Loud.show())
