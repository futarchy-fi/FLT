/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
public import FLT.Mazur.FiniteBaseLocalizedKernels

/-!
# Solutions over arbitrary base denominators from exact numerators

Divide by an element of the original multiplicative set. Unit cancellation
proves the boundary and full mixed equations in the specified localizations.
No principal neighborhood or injective localization map is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
open FiniteBaseLocalizationDenominators
variable {R : Type*} [CommRing R] (M : Submonoid R)
  {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (α : ∀ i, R →+* A i)
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (hα : ∀ i j x, p i j (α i x) = q i j (α j x))
  {S T : ι → Type*} {U : ι → ι → Type*}
  [∀ i, CommRing (S i)] [∀ i, CommRing (T i)] [∀ i j, CommRing (U i j)]
  [∀ i, Algebra (A i) (S i)] [∀ i, Algebra (B i) (T i)]
  [∀ i j, Algebra (C i j) (U i j)]
  [∀ i, IsLocalization (M.map (α i).toMonoidHom) (S i)]
  [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)]
  [∀ i j, IsLocalization (M.map ((p i j).comp (α i)).toMonoidHom) (U i j)]
  (β : ∀ i, S i →+* T i) (π : ∀ i j, S i →+* U i j) (ρ : ∀ i j, S j →+* U i j)
  (hβ : ∀ i x, β i (algebraMap _ _ x) = algebraMap _ _ (φ i x))
  (hπ : ∀ i j x, π i j (algebraMap _ _ x) = algebraMap _ _ (p i j x))
  (hρ : ∀ i j x, ρ i j (algebraMap _ _ x) = algebraMap _ _ (q i j x))

omit [Finite ι]
  [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)]
  [∀ i j, IsLocalization (M.map ((p i j).comp (α i)).toMonoidHom) (U i j)] in
include hα hβ hπ hρ in
/-- Exact numerators construct solutions in the specified base localizations. -/
theorem exists_base_localized_of_numerators (s : M) (w : ∀ i, A i) (t : ∀ i, B i)
    (hb : ∀ i, φ i (w i) = φ i (α i s) * t i)
    (he : ∀ i j, p i j (w i) = q i j (w j)) :
    ∃ v : ∀ i, S i, (∀ i, β i (v i) = algebraMap _ _ (t i)) ∧
      (∀ i j, π i j (v i) = ρ i j (v j)) := by
  let d (i : ι) : M.map (α i).toMonoidHom := ⟨α i s, ⟨s.val, s.property, rfl⟩⟩
  let v (i : ι) : S i := IsLocalization.mk' (S i) (w i) (d i)
  have hv (i : ι) : algebraMap (A i) (S i) (α i s) * v i =
      algebraMap (A i) (S i) (w i) := IsLocalization.mk'_spec' (S i) (w i) (d i)
  refine ⟨v, ?_, ?_⟩
  · intro i
    apply ((FiniteBaseLocalizedKernels.scalar_isUnit M α s i).map (β i)).mul_right_inj.mp
    calc
      _ = β i (algebraMap _ _ (α i s) * v i) := (map_mul _ _ _).symm
      _ = algebraMap _ _ (φ i (w i)) := by rw [hv, hβ]
      _ = _ := by rw [hb, map_mul, hβ]
  · intro i j
    apply ((FiniteBaseLocalizedKernels.scalar_isUnit M α s i).map (π i j)).mul_right_inj.mp
    calc
      _ = π i j (algebraMap _ _ (α i s) * v i) := (map_mul _ _ _).symm
      _ = algebraMap _ _ (p i j (w i)) := by rw [hv, hπ]
      _ = algebraMap _ _ (q i j (w j)) := by rw [he]
      _ = ρ i j (algebraMap _ _ (α j s) * v j) := by rw [hv, hρ]
      _ = _ := by simp only [map_mul, hπ, hρ, ← hα]

end FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
