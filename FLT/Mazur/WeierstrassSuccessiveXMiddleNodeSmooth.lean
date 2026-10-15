/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeCoordinates
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.PolygonAtlasSmoothLocus
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The exact smooth locus of the full localized middle node

For every conic constant, the original localized incidence node is smooth
exactly away from the simultaneous vanishing of its two branch coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (c : K)
local notation "B" => SuccessiveIncidence.Coordinate (0 : K)
local notation "N" => MiddleNodeOpen c
local notation "A" => PolygonNodeEqualizer.A (R := K)

/-- The whole localized middle node embeds in the original polynomial-pair node. -/
def middleNodeToPolygon : Spec (.of N) ⟶ PolygonNodeBranches.node K :=
  PrincipalOpenTransport.inclusion (middleNodeDenominator c) ≫
    (Scheme.Spec.mapIso NodalFiber.polygonNodeEquiv.toRingEquiv.toCommRingCatIso.op).inv

instance middleNodeToPolygon_isOpenImmersion : IsOpenImmersion (middleNodeToPolygon c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The full node comparison preserves its original field structure. -/
@[reassoc] theorem middleNodeToPolygon_structure :
    middleNodeToPolygon c ≫ PolygonNodeBranches.toBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  change algebraMap B N (NodalFiber.polygonNodeEquiv.symm (algebraMap K A a)) = _
  rw [AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply K B N a).symm

/-- Both ordered branch coordinates survive the comparison with the standard node. -/
theorem middleNodeToPolygon_coordinates (z : Spec (.of N)) :
    (PolygonNodeLocalization.x ∈ (middleNodeToPolygon c z).asIdeal ↔
      middleNodeZ c ∈ z.asIdeal) ∧
    (PolygonNodeLocalization.y ∈ (middleNodeToPolygon c z).asIdeal ↔
      middleNodeU c ∈ z.asIdeal) := by
  change (algebraMap B N (NodalFiber.polygonNodeEquiv.symm
      PolygonNodeLocalization.x) ∈ z.asIdeal ↔ _) ∧
    (algebraMap B N (NodalFiber.polygonNodeEquiv.symm
      PolygonNodeLocalization.y) ∈ z.asIdeal ↔ _)
  rw [← NodalFiber.polygonNodeEquiv_p, ← NodalFiber.polygonNodeEquiv_q,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The full localized node has no smooth point at the intersection of its branches. -/
theorem middleNode_mem_smooth_iff (z : Spec (.of N)) :
    z ∈ (Spec.map (CommRingCat.ofHom (algebraMap K N))).smoothLocus ↔
      middleNodeZ c ∉ z.asIdeal ∨ middleNodeU c ∉ z.asIdeal := by
  have hs := PolygonAtlas.mem_smooth_iff (middleNodeToPolygon c)
    (PolygonNodeBranches.toBase K) z
  simp only [middleNodeToPolygon_structure] at hs
  rw [← hs]
  change middleNodeToPolygon c z ∈
    ((PolygonNodePresentation.aToBase K).smoothLocus : Set _) ↔ _
  rw [PolygonNodePresentation.a_smooth_complement,
    ← PolygonNodePresentation.a_zeroLocus_origin]
  change ¬ {PolygonNodeLocalization.x, PolygonNodeLocalization.y} ⊆
    ((middleNodeToPolygon c z).asIdeal : Set A) ↔ _
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, not_and_or]
  exact or_congr (not_congr (middleNodeToPolygon_coordinates c z).1)
    (not_congr (middleNodeToPolygon_coordinates c z).2)

end FLT.Mazur.WeierstrassSuccessiveX
