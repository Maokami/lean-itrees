import ITree.ITree
import ITree.Iter
import ITree.Notation.Iter

namespace ITree

/-
  # Effects
-/

def trigger (e : E A) : ITree E A := .vis e .ret

/-- No effects. This is essentially `Empty`. -/
def None : Type -> Type := fun _ => Empty
@[reducible] instance : EmptyCollection (Type -> Type) := ⟨None⟩
@[reducible] instance : OfNat (Type -> Type) 0 where ofNat := None

/-- The union of two event types. -/
inductive EffProd (E F : Type -> Type) : Type -> Type
| left  : E A -> EffProd E F A
| right : F A -> EffProd E F A
infixl:60 " & " => EffProd

def EffNProd (Es : List (Type -> Type)) : (Type -> Type) :=
  fun Ans => (i : Fin Es.length) -> Es[i] Ans


/-- Asserts that the collection of events `F` has event `E`. -/
class SubEff (E : semiOutParam (Type -> Type)) (F : Type -> Type) where
  injEv : {A : Type} -> E A -> F A

export SubEff (injEv)

variable {E F G : Type -> Type}
variable {A : Type}

instance instCoeEff [SubEff E F] : Coe (E A) (F A) := ⟨injEv⟩
attribute [coe] injEv
instance instHasEff_id : SubEff E E := ⟨id⟩
instance instHasEff_left : SubEff E (E & F) := ⟨.left⟩
instance instHasEff_right : SubEff F (E & F) := ⟨.right⟩

instance [i : SubEff E F] [j : SubEff F G] : SubEff E G where
  injEv := j.injEv ∘ i.injEv

/-
  # Interp, Handlers
  The ITree paper just defines one `interp` using `iter`, for which you can then obtain concrete
  interpretations by giving it a `h`andler.
-/

variable {M : Type -> Type u} [Monad M] [Iter M]

/-- Handles events `E` by interpreting them into the output monad `M`.
  For example, `Handler (Mem Γ) (StateT ..)` -/
def Handler (E : Type -> Type) (M : Type -> Type u) : Type _ :=
  ⦃A : Type⦄ -> E A -> M A

/-- Interpreting events into another monad, which may again be the ITree monad but with e.g.
  fewer or different effects. -/
@[irreducible] -- remove this irreducible tag after interp has been implemented
def interp [Monad M] [Iter M] (h : Handler E M) : ITree E A -> M A :=
  -- Iter.iter (A := ITree E A) (B := ULift A) <|
  --   ITree.cases (E:=E) (A:=A) (motive := fun _ => ITree E ((ITree E A) ⊕ A)) -- ! Need universe-polymorphic ITrees for this. Alternatively, maybe a direct definition of `interp` with `corec`, without relying on `iter` will suffice?
  --     (fun (a : A) => return Sum.inr a)
  --     (fun t => return Sum.inl t)
  --     (fun e k => h e >>= fun ans => return Sum.inl (k ans))
  sorry

variable {h : Handler E M}
@[simp] theorem interp_pure : interp h (return a : ITree E A) = return a := by sorry
@[simp] theorem interp_trigger : interp h (trigger e) = h e := by sorry
@[aesop 80%] theorem interp_bind : interp h (a >>= b) = (interp h a) >>= (fun a => interp h (b a)) := by sorry
@[aesop 1%] theorem interp_iter {f : A → ITree E (A ⊕ B) } : interp h (Iter.iter f a) = Iter.iter (fun a => interp h (f a)) a := by sorry
@[aesop unsafe 10%] theorem interp_ite [Decidable φ] : interp h (if φ then t else e) = (if φ then interp h t else interp h e) := by
  split <;> simp_all only

@[simp] theorem interp_spin [Monad M] [Iter M] {h : Handler E M} : interp h spin = (spin : M A) := sorry
@[simp] theorem interp_spin' [Monad M] [Iter M] {h : Handler E M} {b : A -> ITree E B} : interp h (spin >>= b) = (spin : M B) := sorry

/-
  ## Collection of common `Handler`s
  Figure 10 in the ITree paper.
-/

def Handler.id : Handler E (ITree E) := fun _ => trigger
def Handler.none : Handler None M := fun _ e => nomatch e
def Handler.lift [MonadLiftT N M] (h : Handler E N) : Handler E M         := fun _ e => liftM (h e)
def Handler.inj  [SubEff E F]                       : Handler E (ITree F) := fun _ e => trigger (injEv e)

/-- If our target monad is capable of `E` events, we have a trivial handler for `E` events. -/
def Handler.trivial [MonadLiftT (ITree E) M] : Handler E M := Handler.lift Handler.id

/-- We can embed an ITree with fewer effects into an ITree with more effects. -/
instance [SubEff E F] : MonadLift (ITree E) (ITree F) where
  monadLift := interp Handler.inj

def Handler.inl : Handler E (ITree (E & F)) := fun _ e => trigger (.left e)
def Handler.inr : Handler F (ITree (E & F)) := fun _ e => trigger (.right e)

/-- Related to `EffProd`. -/
def Handler.case (he : Handler E M) (hf : Handler F M) : Handler (E & F) M := fun _ e =>
  match e with
  | .left e => he e
  | .right f => hf f

def Handler.comp (f : Handler E (ITree F)) (g : Handler F (ITree G)) : Handler E (ITree G) :=
  fun _ e => interp g (f e)

def Handler.right [MonadLiftT (ITree E) M] (h : Handler F M) : Handler (E & F) M := Handler.case trivial h
def Handler.left  [MonadLiftT (ITree F) M] (h : Handler E M) : Handler (E & F) M := Handler.case h trivial



variable {he : Handler E M} {hf : Handler F M}
theorem interp_case_left : interp (Handler.case he hf) (trigger (.left e)) = he e := by
  rw [interp_trigger]; rfl
theorem interp_case_right : interp (Handler.case he hf) (trigger (.right f)) = hf f := by
  rw [interp_trigger]; rfl

/-
  ## `SubHandler`
  Sometimes you need to `interp` only a subset of effects.

  This is not used anywhere, and can probably be deleted.
-/

/-- A handler `h` responsible for handling multiple effects `F` can be composed of smaller handlers.
  This typeclass allows you to get just the handler for handling effect `E`. -/
class SubHandler (E : semiOutParam (Type -> Type)) [SubEff E F] (h : Handler F M) where
  subHandler : Handler E M
  lawful {A : Type} {e : E A} : h (injEv e) = subHandler e
export SubHandler (subHandler)
attribute [aesop 90%] SubHandler.lawful

@[aesop 10%] theorem interp_sub [SubEff E F] [SubHandler E hf] {e : E A}
  : interp hf (trigger (injEv e)) = interp (subHandler hf) (trigger e)
  := by simp only [interp_trigger, SubHandler.lawful]

instance [SubHandler E h] : SubHandler E h where
  subHandler := h
  lawful := rfl

variable {L R : Type -> Type} {hl : Handler L M} {hr : Handler R M} [SubEff E L]

instance : SubHandler E (Handler.case he hf) where
  subHandler := he
  lawful := by simp only [Handler.case, implies_true]

instance : SubHandler F (Handler.case he hf) where
  subHandler := hf
  lawful := by simp only [Handler.case, implies_true]

instance [MonadLiftT (ITree F) M] : SubHandler E (Handler.left (F := F) he) where
  subHandler := he
  lawful := by simp only [Handler.left, Handler.case, implies_true]

instance [MonadLiftT (ITree F) M] : SubHandler F (Handler.left (F := F) he) where
  subHandler := Handler.trivial
  lawful := by simp only [Handler.left, Handler.case, implies_true]

instance [MonadLiftT (ITree E) M] : SubHandler F (Handler.right (E := E) hf) where
  subHandler := hf
  lawful := by simp only [Handler.right, Handler.case, implies_true]

instance [MonadLiftT (ITree E) M] : SubHandler E (Handler.right (E := E) hf) where
  subHandler := Handler.trivial
  lawful := by simp only [Handler.right, Handler.case, implies_true]
