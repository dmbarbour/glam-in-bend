# Written by Blend from override.blend; do not edit.
import Base

# blend: override.blend:6
def Greeter.greet() -> String:
  "hello"

# blend: override.blend:8
def Greeter.show() -> String:
  Greeter.greet() ++ ", world"

# blend: override.blend:12
def Loud.greet() -> String:
  "HELLO"

# blend: override.blend:8
def Loud.show() -> String:
  Loud.greet() ++ ", world"

# blend: override.blend:15
def main() -> IO(Unit):
  IO.print(Greeter.show() ++ " / " ++ Loud.show())
