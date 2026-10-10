/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedRecovery
public import FLT.Mazur.PolygonVeroneseAdicProjSquare
public import FLT.Mazur.GradedProjZeroMapNaturality
public import FLT.Mazur.SectionRetainedProjBaseCoefficients

/-!
# The retained polygon stage has its original adic base map

The compatible evaluation preserves the original complete coefficients.
Cancellation of the adic closed immersion identifies the two stage base
maps through the specified power-series quotient equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family compatibleEval
  SectionRetainedProjConstruction.toProj SectionRetainedProjStructuralMap.toBase
  exactVeroneseTensorReduction exactVeroneseStep Proj.map GradedProjRingEquiv.iso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Evaluation into the compatible Proj retains the original power-series structure map. -/
@[reassoc]
theorem boundaryVeroneseProjToCompatible_toBase (m : ℕ) :
    boundaryVeroneseProjToCompatible K n h m ≫ exactVeroneseProjToBase K n h =
      boundaryRetainedProjToOriginalBase K n h m ≫ baseToSeries K m := by
  rw [boundaryRetainedProjToOriginalBase, baseToSeries,
    SectionRetainedProjBaseCoefficients.toBase_specMap]
  apply GradedProjZeroMapNaturality.map_toSpec
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
    (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m)
  intro r
  apply Subtype.ext
  change compatibleVeroneseEval K n h (exactVeroneseStep K n h) m
    (algebraMap (PowerSeries K) (CompatibleVeroneseSections K n h
      (exactVeroneseStep K n h)) r) =
      SectionGradedSum.of (boundaryLine K m n h) ⊤ 0
        (stageScalars K m n h (seriesToStage K m r))
  rw [compatibleVeroneseEval_algebraMap, boundarySeriesScalars_stage]
  rfl

/-- The original truncated base is canonically isomorphic to the specified adic quotient base. -/
def stageAdicBaseIso (m : ℕ) :
    Spec (.of (Ring K m)) ≅ Spec (.of (PowerSeries K ⧸ parameterIdeal K ^ (m + 1))) :=
  Scheme.Spec.mapIso (seriesQuotientEquiv K m).toRingEquiv.toCommRingCatIso.op

/-- The coefficient comparison retains the original map from the complete coefficient ring. -/
@[reassoc]
theorem stageAdicBaseIso_toSeries (m : ℕ) :
    (stageAdicBaseIso K m).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries K) (PowerSeries K ⧸ parameterIdeal K ^ (m + 1)))) =
        baseToSeries K m := by
  change Spec.map (CommRingCat.ofHom (seriesQuotientEquiv K m).toRingHom) ≫
    Spec.map (CommRingCat.ofHom _) = _
  rw [baseToSeries, ← Spec.map_comp]
  congr 1

/-- The W208 adic base map is the original base map under the actual coefficient isomorphism. -/
@[reassoc]
theorem boundaryRetainedProjToOriginalBase_adic (m : ℕ) :
    boundaryRetainedProjToOriginalBase K n h m ≫ (stageAdicBaseIso K m).hom =
      boundaryVeroneseProjToAdicBase K n h m := by
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (PowerSeries K) (PowerSeries K ⧸ parameterIdeal K ^ (m + 1))))
  have : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)
  apply (cancel_mono j).mp
  rw [Category.assoc, stageAdicBaseIso_toSeries,
    ← boundaryVeroneseProjToCompatible_toBase]
  exact (exactVeroneseProj_adic_isPullback K n h m).w

end FLT.Mazur.PolygonInfinitesimalStages
