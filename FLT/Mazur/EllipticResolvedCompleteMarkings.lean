/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedCompleteFiberComparison
public import FLT.Mazur.PolygonCompleteMarkedClosedFiber

/-!
# Original marked residue sections under the complete-family comparison

The unit point on every actual arithmetic component maps to the closed
restriction of the original complete-family marking with the same label.
These are geometric residue sections. Their construction does not assert a
lift to generic torsion points over an arbitrary valuation field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonPinching PolygonInfinitesimalStages ProjectiveLineActionSpecialization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
  completeClosedPolygon_lfp
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "pA" => resolvedSplitStructure A D

/-- The coordinate-one residue section on the actual arithmetic component with its natural label. -/
def resolvedAtlasMarkedPoint (i : Fin depth) : Spec (.of F) ⟶ (pA).smoothLocus.toScheme :=
  unitPoint F 1 ≫ resolvedOrientedComponentChart A D r i

/-- Every chosen point is a section of the original residue-field structure. -/
@[reassoc] theorem resolvedAtlasMarkedPoint_structure (i : Fin depth) :
    resolvedAtlasMarkedPoint A D r i ≫ (pA).smoothLocus.ι ≫ pA = 𝟙 _ := by
  rw [resolvedAtlasMarkedPoint, Category.assoc, resolvedOrientedComponentChart_structure]
  exact unitPoint_base F 1

/-- Distinct natural labels give distinct actual arithmetic residue sections. -/
theorem resolvedAtlasMarkedPoint_injective :
    Function.Injective (resolvedAtlasMarkedPoint A D r) := by
  intro i j he
  by_contra hij
  have he' := congrArg (fun f => f (default : Spec (.of F))) he
  exact Set.disjoint_left.mp (resolvedOrientedComponentCharts_disjoint A D r i j hij)
    ⟨unitPoint F 1 default, rfl⟩ ⟨unitPoint F 1 default, he'.symm⟩

/-- The zero-labeled marking is the actual proper specialization of the arithmetic identity. -/
theorem resolvedAtlasMarkedPoint_zero :
    resolvedAtlasMarkedPoint A D r ⟨0, D.depth_pos⟩ = resolvedSplitSmoothPoint A D 0 := by
  classical
  rw [resolvedAtlasMarkedPoint, resolvedOrientedComponentChart_zero]
  simpa only [map_zero, toMul_zero, ZeroMemClass.coe_zero] using
    resolvedReciprocalIdentitySmoothChart_point A D (0 : ellipticE0 A W)

variable (hd : 2 ≤ depth) [NeZero depth]
local notation "pC" => exactVeroneseProjToBase F depth hd
local notation "p" => PolygonCyclicAtlas.normalization F depth hd
local notation "q" => PolygonCyclicAtlas.nodes F depth hd
local notation "hp" => PolygonCyclicPushout.isPushout F depth hd D.depth_pos
local notation "c" => PolygonCyclicAtlas.toBase F depth hd

/-- The actual marked residue section becomes the original polygon's normalization marking. -/
@[reassoc] theorem resolvedCompletePolygonIso_marking (i : Fin depth) :
    resolvedAtlasMarkedPoint A D r i ≫ (resolvedCompletePolygonIso A D r hd).hom ≫
        (c).smoothLocus.ι = PolygonMarkedSections.sectionMap F depth p 1 i := by
  change (unitPoint F 1 ≫ resolvedOrientedComponentChart A D r i) ≫
    (resolvedPolygonSmoothIso A D r p q hp).hom ≫ _ = _
  rw [Category.assoc]
  exact congrArg (fun f => unitPoint F 1 ≫ f)
    (resolvedPolygonSmoothIso_chart_inclusion A D r p q hp i)

/-- In the original complete family it is exactly the closed restriction of the same marking. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_marking (i : Fin depth) :
    resolvedAtlasMarkedPoint A D r i ≫ (resolvedCompleteSmoothFiberIso A D r hd).hom ≫
        pullback.fst _ _ ≫ (pC).smoothLocus.ι =
      completeClosedBase F ≫ completeBaseMarking F depth hd i := by
  rw [resolvedCompleteSmoothFiberIso, Iso.trans_hom, Category.assoc,
    completeClosedSmoothFiberIso_fst_assoc, completeClosedSmoothInclusion_inclusion,
    resolvedCompletePolygonIso_marking_assoc, completeClosedBase_marking]

/-- Actual proper specialization retains its original smooth character in the complete chart. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_specialization
    [DecidableEq (ResidueField A)] (P : ellipticE0 A W) :
    resolvedSplitSmoothPoint A D P.val ≫ (resolvedCompleteSmoothFiberIso A D r hd).hom ≫
        pullback.fst _ _ = unitPoint F (Additive.toMul (splitDepthSmoothCharacter D P)) ≫
          completePointIdentityClosedTorus F depth hd (0 : Fin depth) ≫
            (completeIdentityChart F depth hd 0 0).left := by
  rw [← resolvedReciprocalIdentitySmoothChart_point A D P, Category.assoc,
    resolvedCompleteSmoothFiberIso_identity]

end FLT.Mazur.WeierstrassDividedDepth
