/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousState

/-!
# Raw arithmetic states for the entire retained chain

There are n internal incoming edges, n+1 retained nodes on each branch, and
one common terminal. The original initial base remains separate from all
internal and closing edges. Compatibility and normalization are predicates.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
variable (R : Type*) [CommRing R] (π : R) (n : ℕ)

/-- The actual edge positions of the retained chain, including both boundary edges. -/
inductive Edge where
  /-- The edge from the original initial open to the first retained node. -/
  | initial
  /-- An internal edge between consecutive retained nodes. -/
  | incoming (i : Fin n)
  /-- The edge from the last retained node to the common terminal. -/
  | closing

/-- Actual smoothings and full Laurent overlaps for every node and edge in the chain. -/
structure State where
  /-- The initial-node smoothing on either branch. -/
  initial : (m : ℕ) → Bool → Quotient R π m
  /-- The actual smoothing of each retained node on either branch. -/
  retained : (m : ℕ) → Fin (n + 1) → Bool → Quotient R π m
  /-- The one common terminal smoothing. -/
  terminal : (m : ℕ) → Quotient R π m
  /-- Every complete overlap, including both original boundary edges. -/
  edgeEquiv : Edge n → (m : ℕ) → Bool →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]

variable {R π n}

/-- Every actual smoothing and complete edge retains its coefficient quotient square. -/
def State.Compatible (S : State R π n) : Prop :=
  (∀ m b, restriction R π m (S.initial (m + 1) b) = S.initial m b) ∧
  (∀ m i b, restriction R π m (S.retained (m + 1) i b) = S.retained m i b) ∧
  (∀ m, restriction R π m (S.terminal (m + 1)) = S.terminal m) ∧
  (∀ e b, CompatibleEquiv (fun m ↦ S.edgeEquiv e m b))

/-- The top arithmetic power annihilates every actual node smoothing. -/
def State.Annihilated (S : State R π n) : Prop :=
  (∀ m b, parameter R π m ^ m * S.initial m b = 0) ∧
  (∀ m i b, parameter R π m ^ m * S.retained m i b = 0) ∧
  (∀ m, parameter R π m ^ m * S.terminal m = 0)

variable (B : (m : ℕ) →
  (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])

/-- Keep the complete original base only at the initial edge. -/
def edgeBase : Edge n → (m : ℕ) →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]
  | .initial, m => B m
  | .incoming _, _ => AlgEquiv.refl
  | .closing, _ => AlgEquiv.refl

/-- Every boundary and internal overlap equals its intended complete base at this order. -/
def State.Normalized (S : State R π n) (r : ℕ) : Prop :=
  ∀ e b, S.edgeEquiv e r b = edgeBase B e r

/-- The full measured error at every actual retained-chain edge. -/
def State.error (S : State R π n) (e : Edge n) (b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (S.edgeEquiv e m b).trans (edgeBase B e m).symm

/-- Both identity bases and the original initial base respect the arithmetic quotients. -/
theorem edgeBase_compatible (hB : CompatibleEquiv B) (e : Edge n) :
    CompatibleEquiv (edgeBase B e) := by
  cases e with
  | initial => exact hB
  | incoming i => intro m; rfl
  | closing => intro m; rfl

/-- Measuring each full edge relative to its own base retains the coefficient square. -/
theorem State.error_compatible (S : State R π n) (hS : S.Compatible)
    (hB : CompatibleEquiv B) (e : Edge n) (b : Bool) :
    CompatibleEquiv (S.error B e b) := by
  intro m
  apply punctureEquiv_trans_naturality
  · exact hS.2.2.2 e b m
  · exact LaurentUnitSubstitutionNaturality.symm_naturality _ _ _ (edgeBase_compatible B hB e m)

/-- Normalization of each original edge makes its whole measured error the identity. -/
theorem State.error_normalized (S : State R π n) (r : ℕ)
    (hr : S.Normalized B r) (e : Edge n) (b : Bool) :
    S.error B e b r = AlgEquiv.refl := by
  unfold State.error
  rw [hr e b]
  ext z : 1
  exact (edgeBase B e r).symm_apply_apply z

end FLT.Mazur.PolygonArithmeticRetainedChain
