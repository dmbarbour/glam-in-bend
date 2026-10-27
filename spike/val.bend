import Base

# glam values, as far as the spike needs them: grown step by step.
type Val is Data:
  VUnit{}
  VNum{+n: U32}
  VLazy{+h: U32}

# what a store slot carries beside its four words
type Pay is Data:
  PNone{}
  PVal{v: Val}
