# Written by Blend from prior.blend; do not edit.
import Base

def Plain.tag() -> String:
  "plain"

def Bold.tag.Plain() -> String:
  "plain"

def Bold.tag() -> String:
  "*" ++ Bold.tag.Plain() ++ "*"

def Loud.tag.Plain() -> String:
  "plain"

def Loud.tag() -> String:
  Loud.tag.Plain() ++ "!"

def BoldLoud.tag.Plain() -> String:
  "plain"

def BoldLoud.tag.Loud() -> String:
  BoldLoud.tag.Plain() ++ "!"

def BoldLoud.tag() -> String:
  "*" ++ BoldLoud.tag.Loud() ++ "*"

def main() -> IO(Unit):
  IO.print(Plain.tag() ++ " " ++ Bold.tag() ++ " " ++ Loud.tag() ++ " " ++ BoldLoud.tag())
