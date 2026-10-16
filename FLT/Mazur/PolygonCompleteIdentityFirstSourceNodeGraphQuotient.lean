/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeCubicCoverage
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# Original source-node quotients factor through the full graph

An affine ideal containing the full original graph ideal defines an actual
map into that graph. When it also contains both source coordinates, this map
is compatible with the existing source-only localization quotient lift.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
variable (I : Ideal Γ(completeIdentityActionAdicChartSpace K n h 1 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1))
variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U) ≤ I)

/-- The unchanged quotient by any ideal containing the full graph ideal maps to the graph. -/
def completeIdentityFirstSourceNodeQuotientToGraph :
    Spec (.of (Γ((R), (V).1) ⧸ I)) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)) ≫
    (f).ker.subschemeCover.f (V) ≫ inv (f).toImage

include hI

/-- The constructed map recovers the original affine quotient's ambient inclusion. -/
@[reassoc] theorem completeIdentityFirstSourceNodeQuotientToGraph_inclusion :
    completeIdentityFirstSourceNodeQuotientToGraph K n h U I hI ≫ (f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (V).2.fromSpec := by
  have hk : inv (f).toImage ≫ (f) = (f).ker.subschemeι := by
    apply (cancel_epi (f).toImage).mp
    rw [IsIso.hom_inv_id_assoc]
    exact (f).toImage_imageι.symm
  rw [completeIdentityFirstSourceNodeQuotientToGraph, Category.assoc, Category.assoc, hk,
    Scheme.IdealSheafData.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]

variable (hx : completeIdentityFirstPoleSource K n h U (leftCoordinate (parameter K 1)) ∈ I)
variable (hy : completeIdentityFirstPoleSource K n h U (rightCoordinate (parameter K 1)) ∈ I)
local notation "φ" => completeIdentityFirstSourceNodeQuotientLift K n h U I hx hy

include hx hy

/-- The quotient's full-graph map is exactly compatible with the source-only localization. -/
theorem completeIdentityFirstSourceNodeQuotientToGraph_sourcePole :
    completeIdentityFirstSourceNodeQuotientToGraph K n h U I hI ≫ (f) =
      Spec.map (CommRingCat.ofHom (φ)) ≫ (M) ≫ (V).1.ι := by
  have he : (φ).comp (algebraMap Γ((R), (V).1)
      (CompleteIdentityFirstSourcePolePatch K n h U)) = Ideal.Quotient.mk I := by
    apply RingHom.ext
    exact completeIdentityFirstSourceNodeQuotientLift_algebraMap K n h U I hx hy
  rw [completeIdentityFirstSourceNodeQuotientToGraph_inclusion,
    completeIdentityFirstSourcePolePatchMap, AffineOpenSpectrumFunctions.map]
  simp only [Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    he, IsAffineOpen.isoSpec_inv_ι]

end FLT.Mazur.PolygonInfinitesimalStages
