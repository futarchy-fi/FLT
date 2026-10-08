/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRestrictionCoordinates

/-!
# Literal old-coordinate targets under fan refinement

A commuting fan refinement transports each old restriction denominator to
exactly the new fan denominator. Its literal iterated target therefore has a
canonical algebra equivalence with the restriction target of the refined fan.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}
  {x y : PrincipalFanStage a b f}

/-- Refinement takes the actual old coordinate denominator to the new coordinate denominator. -/
theorem principalFanRestrictionDenominator_transition (h : x ≤ y) (i j : ι) :
    principalTransition (b j) (principalFan_target_mono h j)
      (principalFanRestrictionDenominator x i j) =
        principalFanRestrictionDenominator y i j := by
  have he := AlgHom.congr_fun (principalFan_hom_comm h j)
    (FiniteRelationLocalization.numerator (relationIdeal R A)
      (principalRepresentative R A (a j)) x.source (principalRepresentative R A (a i)))
  change y.hom j (FiniteRelationLocalization.transition R _ _ h.1 _) = _ at he
  rw [FiniteRelationLocalization.transition_numerator] at he
  exact he.symm

/-- The refined fan target localizes at the literal transitioned old denominator. -/
theorem principalFanRefinedRestrictionTarget_isLocalization (h : x ≤ y) (i j : ι) :
    IsLocalization.Away (FiniteRelationIterated.denominator R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalFanRestrictionDenominator x i j)
      ⟨y.target j, principalFan_target_mono h j⟩) (PrincipalFanRestrictionTarget y i j) := by
  change IsLocalization.Away
    (principalTransition (b j) _ (principalFanRestrictionDenominator x i j)) _
  rw [principalFanRestrictionDenominator_transition h i j]
  exact inferInstanceAs (IsLocalization.Away (principalFanRestrictionDenominator y i j)
    (Localization.Away (principalFanRestrictionDenominator y i j)))

/-- The literal old-denominator stage is the refined fan's actual restriction target. -/
def principalFanRefinedRestrictionEquiv (h : x ≤ y) (i j : ι) :
    FiniteRelationIterated.Stage R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalFanRestrictionDenominator x i j)
      ⟨y.target j, principalFan_target_mono h j⟩ ≃ₐ[R]
        PrincipalFanRestrictionTarget y i j := by
  let d := FiniteRelationIterated.denominator R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalFanRestrictionDenominator x i j)
    ⟨y.target j, principalFan_target_mono h j⟩
  let _ := principalFanRefinedRestrictionTarget_isLocalization h i j
  exact (IsLocalization.algEquiv (Submonoid.powers d)
    (Localization.Away d) (PrincipalFanRestrictionTarget y i j)).restrictScalars R

/-- The comparison preserves every numerator in the refined target chart. -/
theorem principalFanRefinedRestrictionEquiv_algebraMap (h : x ≤ y) (i j : ι)
    (z : PrincipalStage R (B j) (b j) (y.target j)) :
    principalFanRefinedRestrictionEquiv h i j (algebraMap _ _ z) =
      algebraMap _ (PrincipalFanRestrictionTarget y i j) z := by
  let d := FiniteRelationIterated.denominator R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalFanRestrictionDenominator x i j)
    ⟨y.target j, principalFan_target_mono h j⟩
  let _ := principalFanRefinedRestrictionTarget_isLocalization h i j
  exact (IsLocalization.algEquiv (Submonoid.powers d)
    (Localization.Away d) (PrincipalFanRestrictionTarget y i j)).commutes z

end FLT.Mazur.FiniteTypeRelationModel
