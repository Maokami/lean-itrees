import ITree.ITree
import ITree.Monad
import ITree.RunFinite
import ITree.Notation.Iter

namespace ITree

/-
  ## ITrees form an *iterative* monad
  ITrees paper, page 12.
-/

/-- Repeat a computation until it returns `B`. -/
def iter (body : A -> ITree E (A ⊕ B)) (a₀ : A) : ITree E B :=
  ITree.corec (fun (tab : ITree E (A ⊕ B)) =>
    match tab.dest with
    | .ret (.up (.inl a)) => .tau (body a) -- `iter body a`
    | .ret (.up (.inr b)) => .ret (.up b) -- `ret b`
    | .tau t => .tau t
    | .vis ⟨Ans, e, k⟩ => .vis ⟨Ans, e, k⟩
  ) (body a₀)

instance : Iter (ITree E) := ⟨iter⟩


theorem iter_fp {f : A -> ITree E (A ⊕ B)}
  : iter f a₀ = do let ab <- f a₀
                   match ab with
                   | .inl a => (iter f a)
                   | .inr b => return b
  := by sorry

instance : LawfulIter (ITree E) where
  iter_fp' := iter_fp
  while_fp := sorry
  map_spin := sorry
