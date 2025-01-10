import ITree.Eutt
import Mathlib.Data.Quot

/-
  # Quotient of ITree along Eutt

  Eventually, this should replace the public `ITree`.
-/

open ITree

def QITree (E : Type -> Type) (A : Type) : Type 1 := Quotient (α := ITree E A) ITree.setoid

namespace QITree

def ret (a : A) : QITree E A := Quotient.mk ITree.setoid (ITree.ret a)
def tau (t : QITree E A) : QITree E A := Quotient.liftOn t (⟦ITree.tau ·⟧) (by
  intro t t' h
  have : t.tau ≈ t'.tau := Eutt.tau_congr h
  simp only [eq_rec_constant]
  exact Quotient.sound this
)

opaque QITree.vis_impl (e : E Ans) (k : Ans -> QITree E A) : QITree E A := sorry

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Quot.20lifting.20.60.28_.20-.3E.20T.29.20-.3E.20T.60.20to.20.60.28_.20-.3E.20Q.29.20-.3E.20Q.60/near/484606314
@[implemented_by QITree.vis_impl]
def vis (e : E Ans) (k : Ans -> QITree E A) : QITree E A :=
  Quotient.liftOn (Quotient.choice k) (⟦ITree.vis e ·⟧) (fun _ _ => Quotient.eq.mpr ∘ Eutt.vis)

example (t : QITree E A) : QITree.tau t = t := by
  simp [QITree.tau]
  dsimp [Quotient.liftOn, Quot.liftOn, Quotient.mk]

  sorry

set_option pp.proofs true in
def cases {E : Type -> Type} {A : Type} {motive : QITree E A → Sort u}
    (c_ret : (r : A) → motive (.ret r))
    (c_tau : (x : QITree E A) → motive (.tau x))
    (c_vis : {Ans : Type} -> (e : E Ans) → (k : Ans → QITree E A) → motive (.vis e k))
    (x : QITree E A)
    : motive x
    := Quotient.recOn x
      (ITree.cases
        c_ret
        (fun t => c_tau ⟦t⟧)
        (fun e k =>
          have : (QITree.vis e fun ans => ⟦k ans⟧) = ⟦ITree.vis e k⟧ := by simp only [QITree.vis, Quotient.choice_eq, Quotient.lift_mk]
          this ▸ c_vis e (fun ans => ⟦k ans⟧)))
      (fun a b h => by
        simp
        cases a
        case ret r => -- provable
          cases b
          case ret r => sorry
          case tau t => sorry
          case vis e k => sorry
        case tau t =>
          cases b
          case ret r =>
            simp [ITree.cases_tau, ITree.cases_ret, ITree.cases_vis]
            have h : t ≈ .ret r := sorry
            -- We know that t converges to `.ret r`, and emits no events.
            have := Quotient.sound h
            -- We can obtain any proof `⟦.ret r⟧ = ⟦t⟧ = ⟦t.tau⟧ = ⟦t.tau.tau⟧ = ⟦t.tau.tau.tau⟧ = ...`
            -- By function extensionality (sort of...?) we can know that `c_tau ⟦.ret r⟧ = c_tau ⟦t⟧ = c_tau ⟦t.tau⟧ = ...`

            -- this is not provable... (or only provable if our motive is `... -> Prop`)
            sorry
          case tau t =>
            simp [ITree.cases_tau, ITree.cases_ret, ITree.cases_vis]
            sorry
          case vis e k =>
            simp [ITree.cases_tau, ITree.cases_ret, ITree.cases_vis]
            sorry
        case vis e k =>
          cases b
          case ret r => sorry
          case tau t => sorry
          case vis e k => sorry
      )


-- TODO: corec...
