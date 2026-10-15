/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphParameterTorsion
public import FLT.Mazur.PolygonFirstNodeParameterStructure

/-!
# The original ambient node relation retains the complete coefficient map

The comparison is made before imposing the graph ideal. In particular it
retains the nilpotents in the full original node-pair relation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m
local notation "b" => Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹]))

/-- The full original relation has the source node's actual truncated coefficient map. -/
def completeIdentityAdicAmbientStructure : (R) ⟶ Spec (.of (A)) :=
  pullback.fst _ _ ≫ chartStructure (A)[T;T⁻¹] (LaurentPolynomial.C (t)) ≫ (b)

/-- Its complete coefficient structure is the original truncated structure followed by inclusion. -/
@[reassoc] theorem completeIdentityAdicAmbientStructure_complete :
    (k) ≫ completeIdentityActionLiftSpaceStructure K n h =
      completeIdentityAdicAmbientStructure K n h m i j ≫ baseToSeries K m := by
  rw [completeIdentityActionLiftSpaceStructure, Category.assoc,
    completeIdentityActionAdicLiftSpaceMap, pullback.lift_fst_assoc,
    Category.assoc, completeIdentityActionAdicChartSpaceMap_fst_assoc]
  change (pullback.fst _ _ ≫ PolygonInfinitesimal.chart (A)[T;T⁻¹]
    (LaurentPolynomial.C (t)) n h i) ≫ completeIdentityFiniteInput K n h 0 m ≫
      pullback.snd _ _ ≫ exactVeroneseProjToBase K n h = _
  rw [completeIdentityFiniteInput_snd_assoc, originalStageToCompatibleProj_toBase]
  change (pullback.fst _ _ ≫ PolygonInfinitesimal.chart (A)[T;T⁻¹]
    (LaurentPolynomial.C (t)) n h i) ≫
      parameterProjection LaurentPolynomial.C (t) (LaurentPolynomial.C (t)) rfl n h ≫
        toBase (A) (t) n h ≫ baseToSeries K m = _
  rw [parameterProjection_base_assoc, Category.assoc, chart_toBase_assoc]
  rfl

/-- Moving the Laurent unit preserves the same original ambient coefficients. -/
@[reassoc] theorem completeIdentityFirstAmbientSource_structure :
    (pullback.fst _ _ ≫ (firstNodeParameterIso K).inv :
      completeIdentityActionAdicChartSpace K n h 1 0 0 ⟶ _) ≫
        chartStructure (Ring K[T;T⁻¹] 1) (parameter K[T;T⁻¹] 1) ≫
          Spec.map (CommRingCat.ofHom
            (stageCoefficientMap (LaurentPolynomial.C : K →+* K[T;T⁻¹]) 1)) =
      completeIdentityAdicAmbientStructure K n h 1 0 0 := by
  rw [Category.assoc, firstNodeParameterIso_inv_structure]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
