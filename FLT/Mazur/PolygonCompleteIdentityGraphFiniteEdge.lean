/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraph
public import FLT.Mazur.PolygonCompleteIdentityActionSmoothCompatibility
public import FLT.Mazur.PolygonCompleteIdentityFinitePair

/-!
# The original finite identity edge maps to the complete cubic graph

Factor the actual original finite input through the unchanged smooth-input
domain and then through its complete graph. Its graph target is proved to be
original multiplication, using the original restricted cubic isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "V" => completeIdentityActionUnchangedOpen K n h (0 : Fin n)
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (0 : Fin n)
local notation "f" => completeIdentityFiniteInput K n h (0 : Fin n) m
local notation "M" => completeIdentityFiniteOriginalMul K n h (0 : Fin n) m
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)

/-- The original entire finite identity edge lies in the unchanged cubic-action domain. -/
def completeIdentityFiniteEdgeToUnchanged :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι ((j) ≫ (f)) (by
    rw [Scheme.Opens.range_ι, completeIdentityActionUnchangedOpen_eq]
    rintro _ ⟨x, rfl⟩
    change (((j) ≫ (f)) ≫ completeIdentityActionSecond K n h) x ∈ (U)
    rw [Category.assoc, completeIdentityFiniteEdge_snd]
    exact (((Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
      (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])))) ≫
        completeIdentityStageTorus K n h 0 m) x).2)

/-- This is the exact original finite input, with both original parameters. -/
@[reassoc] theorem completeIdentityFiniteEdgeToUnchanged_input :
    completeIdentityFiniteEdgeToUnchanged K n h m ≫ (V).ι = (j) ≫ (f) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The unchanged cubic lift is exactly actual original multiplication on the finite edge. -/
@[reassoc] theorem completeIdentityFiniteEdgeToUnchanged_mul :
    completeIdentityFiniteEdgeToUnchanged K n h m ≫
      completeIdentityActionUnchangedLift K n h 0 = (M) := by
  apply (cancel_mono (completePointSmoothCubicIso K n h 0).hom).mp
  apply (cancel_mono (integralSmoothOpen (completePointWeierstrassCurve K n h 0)).ι).mp
  simp only [Category.assoc, completePointSmoothCubicIso_inclusion]
  rw [completeIdentityActionUnchangedLift_contraction,
    completeIdentityFiniteEdgeToUnchanged_input_assoc,
    completeIdentityFiniteOriginalMul_cubic]

/-- The original finite edge maps into the complete graph with its actual full ideal. -/
def completeIdentityFiniteEdgeToGraph :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphClosure K n h :=
  completeIdentityFiniteEdgeToUnchanged K n h m ≫
    completeIdentityActionUnchangedToSmooth K n h ≫ completeIdentityActionSmoothToGraph K n h

/-- The constructed graph point lies over precisely the original finite edge input. -/
@[reassoc] theorem completeIdentityFiniteEdgeToGraph_source :
    completeIdentityFiniteEdgeToGraph K n h m ≫ completeIdentityActionGraphProjection K n h =
      (j) ≫ (f) := by
  rw [completeIdentityFiniteEdgeToGraph, Category.assoc, Category.assoc,
    completeIdentityActionSmoothToGraph_projection,
    completeIdentityActionUnchangedToSmooth_inclusion,
    completeIdentityFiniteEdgeToUnchanged_input]

/-- Its complete polygon coordinate is the original group product, including nilpotents. -/
@[reassoc] theorem completeIdentityFiniteEdgeToGraph_target :
    completeIdentityFiniteEdgeToGraph K n h m ≫ completeIdentityActionGraphLift K n h =
      (M) ≫ (U).ι := by
  rw [completeIdentityFiniteEdgeToGraph, Category.assoc, Category.assoc,
    completeIdentityActionSmoothToGraph_lift, completeIdentityActionSmoothLift_unchanged,
    completeIdentityFiniteEdgeToUnchanged_mul_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
