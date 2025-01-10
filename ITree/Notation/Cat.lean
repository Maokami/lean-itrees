/-- Concatenation of continuations. Provides the `>>>` notation. -/
class Cat (K : Type u -> Type u -> Type u) where
  cat : K A B -> K B C -> K A C
infixl:75 " >>> " => Cat.cat
