/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientLifts

/-!
# Higher affine quotients factor through the full original graph

Every affine ideal containing the full original graph ideal defines a map
into that graph at every positive stage. Neither source coordinates nor the
parameter are required to vanish.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
variable (I : Ideal Γ(completeIdentityActionAdicChartSpace K n h (m + 1) 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1))
variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U) ≤ I)

/-- The unchanged quotient by any ideal containing the full graph ideal maps to the graph. -/
def completeIdentityTopAffineQuotientToGraph :
    Spec (.of (Γ((R), (V).1) ⧸ I)) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)) ≫
    (f).ker.subschemeCover.f (V) ≫ inv (f).toImage

include hI

/-- The constructed map recovers the original affine quotient's ambient inclusion. -/
@[reassoc] theorem completeIdentityTopAffineQuotientToGraph_inclusion :
    completeIdentityTopAffineQuotientToGraph K n h m U I hI ≫ (f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (V).2.fromSpec := by
  have hk : inv (f).toImage ≫ (f) = (f).ker.subschemeι := by
    apply (cancel_epi (f).toImage).mp
    rw [IsIso.hom_inv_id_assoc]
    exact (f).toImage_imageι.symm
  rw [completeIdentityTopAffineQuotientToGraph, Category.assoc, Category.assoc, hk,
    Scheme.IdealSheafData.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]

end FLT.Mazur.PolygonInfinitesimalStages
