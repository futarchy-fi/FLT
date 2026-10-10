/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleZeroNode
public import FLT.Mazur.NodeBranchPushout

/-!
# Scheme pinching on the full zero-constant attachment node

The actual localized attachment ring is used as target, and its original
origin and coefficient structure are retained by the scheme comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K) (hc : c = 0)
local notation "N" => MiddleNodeOpen c

/-- The entire original attachment-node scheme, in its oriented polygon coordinates. -/
def middleNodeIsoOfZero : PolygonNodeBranches.node K ≅ Spec (.of N) :=
  Scheme.Spec.mapIso (middleNodeEquivOfZero c hc).toRingEquiv.toCommRingCatIso.op

/-- The first full normalized affine branch in the original attachment node. -/
def middleNodeFirstBranch : ProjectiveLine.chart K ⟶ Spec (.of N) :=
  PolygonCyclicAtlas.firstBranch K ≫ (middleNodeIsoOfZero c hc).hom

/-- The second full normalized affine branch in the original attachment node. -/
def middleNodeSecondBranch : ProjectiveLine.chart K ⟶ Spec (.of N) :=
  PolygonCyclicAtlas.secondBranch K ≫ (middleNodeIsoOfZero c hc).hom

/-- The original localized attachment scheme is a pushout in schemes, for arbitrary targets. -/
theorem middleNodeBranches_isPushout :
    IsPushout (ProjectiveLine.chartZero K) (ProjectiveLine.chartZero K)
      (middleNodeFirstBranch c hc) (middleNodeSecondBranch c hc) :=
  NodeBranchPushout.isPushout_of_iso K (middleNodeIsoOfZero c hc)

/-- The node comparison preserves the whole original origin map. -/
@[reassoc] theorem middleNodeIsoOfZero_origin :
    PolygonNodePresentation.aOrigin K ≫ (middleNodeIsoOfZero c hc).hom =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : N →ₐ[K] K => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleNodeEquivOfZero_origin c hc)

/-- The actual node comparison is over the original coefficient field. -/
@[reassoc] theorem middleNodeIsoOfZero_structure :
    (middleNodeIsoOfZero c hc).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K N)) = PolygonNodeBranches.toBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (middleNodeEquivOfZero c hc).toAlgHom.comp_algebraMap

/-- The first normalized origin remains the original attachment origin. -/
@[reassoc] theorem middleNodeFirstBranch_origin :
    ProjectiveLine.chartZero K ≫ middleNodeFirstBranch c hc =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) := by
  rw [middleNodeFirstBranch, ← Category.assoc, PolygonCyclicAtlas.zero_firstBranch,
    middleNodeIsoOfZero_origin]

/-- The second normalized origin is the same original attachment origin. -/
@[reassoc] theorem middleNodeSecondBranch_origin :
    ProjectiveLine.chartZero K ≫ middleNodeSecondBranch c hc =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) := by
  rw [middleNodeSecondBranch, ← Category.assoc, PolygonCyclicAtlas.zero_secondBranch,
    middleNodeIsoOfZero_origin]

end FLT.Mazur.WeierstrassSuccessiveX
