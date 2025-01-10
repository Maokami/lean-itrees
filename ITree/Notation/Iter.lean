import Aesop

/-
  # `Iter`ative monads
  This does not (yet) mention `ITree`s, but we can state some properties nonetheles.

  For the actual implementation for `ITree`, see `ITree/Iter.lean`.
-/

/-- The monad `M` is equipped with `iter`.

  Implementing this typeclass automatically gives you a few other goodies, such as `loop`, `While`.
 -/
class Iter (M : Type u -> Type v) extends Monad M where
  /-- Repeat `f` until it returns `B`. -/
  iter : {A B : Type u} -> (f : A -> M (A ⊕ B)) -> (a₀ : A) -> M B

export Iter (iter)

def iterLift [Iter M] (body : A -> M (A ⊕ B)) : (A ⊕ B) -> M (A ⊕ B)
| .inl a => body a
| .inr b => return .inr b

/-- `iterOn a₀ f = iter f a₀`. -/
abbrev iterOn [Iter M] {A B : Type u} (a₀ : A) (f : A -> M (A ⊕ B)) :=
  iter f a₀

/-- Combinator for writing `while` loops, expressed in terms of `iter`.

  Uppercase because `while` is a keyword in Lean. -/
def While [Iter M] (c : M Bool) (body : M Unit) : M Unit :=
  iter (fun () => do
    if (<- c) then
      body
      return .inl ()
    else
      return .inr ()
  )
  ()

def caseM [Monad M] (ca : A -> M C) (cb : B -> M C) (ab : M (A ⊕ B)) : M C := do
  match <- ab with
  | .inl a => ca a
  | .inr b => cb b

def spin [Monad M] [Iter M] : M A := iter (fun () => return .inl ()) ()

class LawfulIter (M : Type /- u -/ -> Type v) [Iter M] : Prop where
  iter_fp' {f : A -> M (A ⊕ B)} {a₀ : A}
    : iter f a₀
    = do
      match <- f a₀ with
      | .inl a => iter f a
      | .inr b => return b
  while_fp {c : M Bool} : While c body = do if (<- c) then body; While c body
  /-- Unroll `iter` once. Note that the first case is `(fun a => iter f a)` instead of `iter f`,
    so that we can apply `iter_fp` multiple times. -/
  iter_fp {f : A -> M (A ⊕ B)} {a₀ : A} : iter f a₀ = caseM (fun a => iter f a) pure (f a₀) := iter_fp'
  iter_fp'' {f : A -> M (A ⊕ B)} : iter f = fun a₀ => caseM (iter f) pure (f a₀) := funext (fun a => iter_fp (a₀ := a))
  map_spin {f : A -> B} : f <$> (spin : M A) = spin

export LawfulIter (iter_fp iter_fp' iter_fp'' while_fp map_spin)

attribute [aesop 10%] iter_fp' while_fp
attribute [simp] map_spin
