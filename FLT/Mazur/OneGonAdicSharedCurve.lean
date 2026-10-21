/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedStage
public import FLT.Mazur.ArithmeticOneGonCommonCoefficientCoherence

/-!
# Full arithmetic comparisons over any shared finite coefficient ring

The shared ring is supplied with actual support inclusions. Equality of its
smoothing parameters constructs comparisons of the full generalized curves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- Compare the actual shared-stage curves through their arithmetic coefficient models. -/
irreducible_def sharedCurveIso :=
  @commonCoefficientIso (base I t ht n s) (base I t ht n u) K _ _ _
    (sharedAlgebra I t ht n s K hS) (sharedAlgebra I t ht n u K hU)
    (parameter I t ht n s) (parameter I t ht n u)
    (parameter_complementaryUnit I t ht n s hs)
    (parameter_complementaryUnit I t ht n u hu)
    (shared_parameter_eq I t ht n s K hS u hU)

omit [Algebra.FiniteType ℤ K] in
/-- Three actual shared-stage full curves satisfy the cocycle equation. -/
@[reassoc] theorem sharedCurveIso_trans (v : Set R) (hV : base I t ht n v ≤ K)
    (hv : complementaryInverse I t ht ∈ v) :
    (sharedCurveIso I t ht n s u K hS hU hs hu).hom ≫
      (sharedCurveIso I t ht n u v K hU hV hu hv).hom =
        (sharedCurveIso I t ht n s v K hS hV hs hv).hom := by
  rw [sharedCurveIso_def, sharedCurveIso_def, sharedCurveIso_def]
  exact @commonCoefficientIso_trans (base I t ht n s) (base I t ht n u)
    (base I t ht n v) K _ _ _ _ (sharedAlgebra I t ht n s K hS)
    (sharedAlgebra I t ht n u K hU) (sharedAlgebra I t ht n v K hV) _ _ _ _ _ _ _ _

/-- A support compared with itself gives the full identity, including the action. -/
theorem sharedCurveIso_refl :
    sharedCurveIso I t ht n s s K hS hS hs hs =
      Iso.refl (stageCurve I t ht n s (sharedStage I t ht n s K hS) hs) := by
  rw [sharedCurveIso_def]
  exact @commonCoefficientIso_refl (base I t ht n s) K _ _
    (sharedAlgebra I t ht n s K hS) _ _

end FLT.Mazur.OneGonAdicIndependentModel
