/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Max Nowak
-/

/-- Concatenation of continuations. Provides the `>>>` notation. -/
class Cat (K : Type u -> Type u -> Type u) where
  cat : K A B -> K B C -> K A C
infixl:75 " >>> " => Cat.cat
