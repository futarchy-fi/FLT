/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopAffineGraphQuotient

/-!
# Full original graph factorization for arbitrary affine receiving rings

A homomorphism killing the full graph ideal defines a map into that same
graph, with exactly its original ambient affine map. No source coordinates
or smoothing parameter are required to vanish for this construction.
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
variable {B : Type} [CommRing B]
variable (ψ : Γ(completeIdentityActionAdicChartSpace K n h (m + 1) 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1) →+* B)
variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U) ≤ RingHom.ker ψ)

/-- The full original graph receives every affine ring test killing its unchanged ideal. -/
def completeIdentityTopAffineTestToGraph :
    Spec (.of B) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (RingHom.ker ψ) ψ
    (fun _ hz ↦ hz))) ≫
    completeIdentityTopAffineQuotientToGraph K n h m U (RingHom.ker ψ) hI

include hI

/-- The factorization recovers the exact original affine ambient morphism. -/
@[reassoc] theorem completeIdentityTopAffineTestToGraph_inclusion :
    completeIdentityTopAffineTestToGraph K n h m U ψ hI ≫ (f) =
      Spec.map (CommRingCat.ofHom ψ) ≫ (V).2.fromSpec := by
  rw [completeIdentityTopAffineTestToGraph, Category.assoc,
    completeIdentityTopAffineQuotientToGraph_inclusion,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

end FLT.Mazur.PolygonInfinitesimalStages
