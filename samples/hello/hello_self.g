language g0

# A function applied to itself: copies of one duplication meet, which fan
# pairing by static labels gets wrong and by GAL levels right
# (lowering-uses-levels). four applies the identity four times.
asm.result = four (\s -> s) "Hello, World!" where
  two = \f x -> f (f x)
  four = (\t -> t t) two
