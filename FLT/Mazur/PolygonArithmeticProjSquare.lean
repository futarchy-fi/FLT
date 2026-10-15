/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageProj
public import FLT.Mazur.PolygonArithmeticTensorReduction
public import FLT.Mazur.GradedProjArbitraryBaseChange
public import FLT.Mazur.GradedProjRingEquivNaturality

/-!
# The original retained stage Proj is the adic base change

The graded tensor-reduction equivalence identifies the stage Proj with the
scalar-extended compatible Proj. The actual evaluation map is the projection,
so the resulting square is Cartesian even for the truncated coefficient base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open GradedProjBaseChangeMap GradedProjStructuralMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseTensorReduction exactVeroneseStep
  boundaryLine family compatibleEval Proj.map GradedProjRingEquiv.iso

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

/-- The original stage Proj is the Proj of the actual coefficient scalar extension. -/
def exactVeroneseStageBaseChangeIso (m : ℕ) :
    boundaryExactVeroneseProj A π n h hne hgen m ≅
      Proj (baseGrade (B := A ⧸ ideal A π ^ (m + 1))
        (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))) :=
  GradedProjRingEquiv.iso _ _ (exactVeroneseTensorReduction A π n h hne hgen m)
    (exactVeroneseTensorReduction_mem_iff A π n h hne hgen m)

/-- Through the actual reduction isomorphism, projection is the original stage evaluation. -/
@[reassoc]
theorem exactVeroneseStageBaseChangeIso_projection (m : ℕ) :
    (exactVeroneseStageBaseChangeIso A π n h hne hgen m).hom ≫
        projection (B := A ⧸ ideal A π ^ (m + 1))
          (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)) =
      boundaryVeroneseProjToCompatible A π n h hne hgen m := by
  have he : (GradedProjRingEquiv.forward _ _ (exactVeroneseTensorReduction A π n h hne hgen m)
        (exactVeroneseTensorReduction_mem_iff A π n h hne hgen m)).comp
      (inclusion (B := A ⧸ ideal A π ^ (m + 1))
        (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))) =
      boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m := by
    ext s : 1
    exact exactVeroneseTensorReduction_one_tmul A π n h hne hgen m s
  unfold exactVeroneseStageBaseChangeIso projection boundaryVeroneseProjToCompatible
  exact GradedProjRingEquivNaturality.iso_hom_map
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))
    (baseGrade (B := A ⧸ ideal A π ^ (m + 1))
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)))
    (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
    (exactVeroneseTensorReduction A π n h hne hgen m)
    (exactVeroneseTensorReduction_mem_iff A π n h hne hgen m)
    (inclusion (B := A ⧸ ideal A π ^ (m + 1))
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)))
    (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m)
    (irrelevant_le_map _)
    (boundaryVeroneseEvaluation_irrelevant A π n h hne hgen m) he

/-- The truncated coefficient structural map, transported through the original reduction. -/
def boundaryVeroneseProjToAdicBase (m : ℕ) :
    boundaryExactVeroneseProj A π n h hne hgen m ⟶
      Spec (.of (A ⧸ ideal A π ^ (m + 1))) :=
  (exactVeroneseStageBaseChangeIso A π n h hne hgen m).hom ≫
    toSpecBase (baseGrade (B := A ⧸ ideal A π ^ (m + 1))
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)))

/-- Each original retained stage Proj is the actual parameter-adic base change of the candidate. -/
theorem exactVeroneseProj_adic_isPullback (m : ℕ) :
    IsPullback (boundaryVeroneseProjToCompatible A π n h hne hgen m)
      (boundaryVeroneseProjToAdicBase A π n h hne hgen m) (exactVeroneseProjToBase A π n h hne hgen)
      (Spec.map (CommRingCat.ofHom (algebraMap (A)
        (A ⧸ ideal A π ^ (m + 1))))) := by
  have hp := GradedProjArbitraryBaseChange.isPullback
    (B := A ⧸ ideal A π ^ (m + 1))
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))
  refine hp.of_iso (exactVeroneseStageBaseChangeIso A π n h hne hgen m).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by simp)
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc] using
      congrArg ((exactVeroneseStageBaseChangeIso A π n h hne hgen m).inv ≫ ·)
        (exactVeroneseStageBaseChangeIso_projection A π n h hne hgen m)
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      boundaryVeroneseProjToAdicBase, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

end FLT.Mazur.PolygonArithmeticStages
