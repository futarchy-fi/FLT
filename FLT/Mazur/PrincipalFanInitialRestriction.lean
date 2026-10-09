/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanOriginalRecovery

/-!
# Initial literal restriction targets

The simultaneous polynomial refinement API starts an iterated localization
at its own relation stage. Its reflexive denominator transition gives the
canonical fan restriction ring, and the comparison preserves projection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)] {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))


variable (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι)

/-- Identify the canonical double-open ring with the literal initial iterated stage. -/
def principalFanInitialRestrictionEquiv :
    PrincipalFanRestrictionTarget x i j ≃ₐ[R]
      FiniteRelationIterated.Stage R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalFanRestrictionDenominator x i j) ⟨x.target j, le_refl (x.target j)⟩ :=
  (principalFanRefinedRestrictionEquiv (le_refl x) i j).symm

/-- The initial comparison fixes all first-localization numerators. -/
theorem principalFanInitialRestrictionEquiv_algebraMap
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    principalFanInitialRestrictionEquiv e x i j (algebraMap _ _ z) = algebraMap _ _ z := by
  apply (principalFanRefinedRestrictionEquiv (le_refl x) i j).injective
  change principalFanRefinedRestrictionEquiv (le_refl x) i j
    ((principalFanRefinedRestrictionEquiv (le_refl x) i j).symm _) = _
  rw [AlgEquiv.apply_symm_apply, principalFanRefinedRestrictionEquiv_algebraMap]

/-- Projection through the literal initial target equals projection of the canonical target. -/
theorem principalFanInitialRestrictionEquiv_projection :
    (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalFanRestrictionDenominator x i j) ⟨x.target j, le_refl (x.target j)⟩).comp
        (principalFanInitialRestrictionEquiv e x i j).toAlgHom =
      principalFanRestrictionProjection e x i j := by
  let _ : IsLocalization.Away (principalFanRestrictionDenominator x i j)
      (PrincipalFanRestrictionTarget x i j) :=
    inferInstanceAs (IsLocalization.Away (principalFanRestrictionDenominator x i j)
      (Localization.Away (principalFanRestrictionDenominator x i j)))
  apply IsLocalization.algHom_ext (Submonoid.powers
    (principalFanRestrictionDenominator x i j))
  apply AlgHom.ext
  intro z
  change FiniteRelationIterated.toQuotient R _ _ _ _ _
    (principalFanInitialRestrictionEquiv e x i j (algebraMap _ _ z)) =
      principalFanRestrictionProjection e x i j (algebraMap _ _ z)
  rw [principalFanInitialRestrictionEquiv_algebraMap,
    FiniteRelationIterated.toQuotient_algebraMap, principalFanRestrictionProjection_algebraMap]

end FLT.Mazur.FiniteTypeRelationModel
