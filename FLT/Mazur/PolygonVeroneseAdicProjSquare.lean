/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageVeroneseProj
public import FLT.Mazur.PolygonVeroneseTensorReduction
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

namespace FLT.Mazur.PolygonInfinitesimalStages

open GradedProjBaseChangeMap GradedProjStructuralMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseTensorReduction exactVeroneseStep
  boundaryLine family compatibleEval Proj.map GradedProjRingEquiv.iso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage Proj is the Proj of the actual coefficient scalar extension. -/
def exactVeroneseStageBaseChangeIso (m : ℕ) :
    boundaryExactVeroneseProj K n h m ≅
      Proj (baseGrade (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
        (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))) :=
  GradedProjRingEquiv.iso _ _ (exactVeroneseTensorReduction K n h m)
    (exactVeroneseTensorReduction_mem_iff K n h m)

/-- Through the actual reduction isomorphism, projection is the original stage evaluation. -/
@[reassoc]
theorem exactVeroneseStageBaseChangeIso_projection (m : ℕ) :
    (exactVeroneseStageBaseChangeIso K n h m).hom ≫
        projection (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
          (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) =
      boundaryVeroneseProjToCompatible K n h m := by
  have he : (GradedProjRingEquiv.forward _ _ (exactVeroneseTensorReduction K n h m)
        (exactVeroneseTensorReduction_mem_iff K n h m)).comp
      (inclusion (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
        (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))) =
      boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m := by
    ext s : 1
    exact exactVeroneseTensorReduction_one_tmul K n h m s
  unfold exactVeroneseStageBaseChangeIso projection boundaryVeroneseProjToCompatible
  exact GradedProjRingEquivNaturality.iso_hom_map
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (baseGrade (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)))
    (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
    (exactVeroneseTensorReduction K n h m)
    (exactVeroneseTensorReduction_mem_iff K n h m)
    (inclusion (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)))
    (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m)
    (irrelevant_le_map _)
    (boundaryVeroneseEvaluation_irrelevant K n h m) he

/-- The truncated coefficient structural map, transported through the original reduction. -/
def boundaryVeroneseProjToAdicBase (m : ℕ) :
    boundaryExactVeroneseProj K n h m ⟶
      Spec (.of (PowerSeries K ⧸ parameterIdeal K ^ (m + 1))) :=
  (exactVeroneseStageBaseChangeIso K n h m).hom ≫
    toSpecBase (baseGrade (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)))

/-- Each original retained stage Proj is the actual parameter-adic base change of the candidate. -/
theorem exactVeroneseProj_adic_isPullback (m : ℕ) :
    IsPullback (boundaryVeroneseProjToCompatible K n h m)
      (boundaryVeroneseProjToAdicBase K n h m) (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K)
        (PowerSeries K ⧸ parameterIdeal K ^ (m + 1))))) := by
  have hp := GradedProjArbitraryBaseChange.isPullback
    (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
  refine hp.of_iso (exactVeroneseStageBaseChangeIso K n h m).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by simp)
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc] using
      congrArg ((exactVeroneseStageBaseChangeIso K n h m).inv ≫ ·)
        (exactVeroneseStageBaseChangeIso_projection K n h m)
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      boundaryVeroneseProjToAdicBase, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

end FLT.Mazur.PolygonInfinitesimalStages
