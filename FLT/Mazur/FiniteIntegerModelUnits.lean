/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.IntegerModelMarkedExtension

/-!
# A common stage for units in finitely many presentation models

Units in different intersection coordinate rings descend simultaneously,
with their inverses, while retaining an initial coefficient stage and all
fixed presentations. This permits later transport of the atlas maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v w

/-- Finitely many unit families in different coordinate rings descend to one larger stage. -/
theorem exists_integer_model_finite_units {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ i, (P i).HasCoeffs A₀]
    (K : I → Type w) [∀ i, Finite (K i)] (x : ∀ i, K i → (B i)ˣ)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ _h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∃ y : ∀ i, K i → ((P i).ModelOfHasCoeffs S)ˣ,
          ∀ i k, (P i).tensorModelOfHasCoeffsEquiv S
            (1 ⊗ₜ (y i k : (P i).ModelOfHasCoeffs S)) = (x i k : B i) := by
  classical
  have hex (i) := exists_integer_model_unit_extension (P i) A₀ (x i) ∅ Set.finite_empty
  choose R hR _ h₀R hPR y hy using hex
  obtain ⟨S, hS, hsS, h₀S, hRS⟩ := exists_common_coefficient_extension A₀ R hR s hs
  let hPS : ∀ i, (P i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (P i) h₀S
  let z : ∀ i, K i → ((P i).ModelOfHasCoeffs S)ˣ := fun i ↦
    letI := hPR i
    fun k ↦ Units.map (integerModelTransition (P i) (hRS i)).toMonoidHom (y i k)
  refine ⟨S, hS, hsS, h₀S, hPS, z, fun i k ↦ ?_⟩
  let := hPR i
  change (P i).tensorModelOfHasCoeffsEquiv S
    (1 ⊗ₜ integerModelTransition (P i) (hRS i) (y i k)) = _
  rw [integerModelTransition_recovery, hy]

end FLT.Mazur.Approximation
