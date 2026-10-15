/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOpen
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.PolygonAtlasSmoothLocus
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The exact smooth locus of the first full attachment node

The original full node is smooth exactly away from the simultaneous
vanishing of its two branch coordinates, retaining both tangent factors.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K)
local notation "B" => NodalFiber.Coordinate (0 : K)
local notation "N" => FullNodeOpen a c
local notation "A" => PolygonNodeEqualizer.A (R := K)

/-- The whole localized first node embeds in the original polynomial-pair node. -/
def fullNodeToPolygon : Spec (.of N) ⟶ PolygonNodeBranches.node K :=
  PrincipalOpenTransport.inclusion (fullNodeDenominator a c) ≫
    (Scheme.Spec.mapIso NodalFiber.polygonNodeEquiv.toRingEquiv.toCommRingCatIso.op).inv

instance fullNodeToPolygon_isOpenImmersion : IsOpenImmersion (fullNodeToPolygon a c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The full node comparison preserves its original field structure. -/
@[reassoc] theorem fullNodeToPolygon_structure :
    fullNodeToPolygon a c ≫ PolygonNodeBranches.toBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change algebraMap B N (NodalFiber.polygonNodeEquiv.symm (algebraMap K A x)) = _
  rw [AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply K B N x).symm

/-- Both ordered branch coordinates survive the comparison with the standard node. -/
theorem fullNodeToPolygon_coordinates (z : Spec (.of N)) :
    (PolygonNodeLocalization.x ∈ (fullNodeToPolygon a c z).asIdeal ↔
      fullNodeP a c ∈ z.asIdeal) ∧
    (PolygonNodeLocalization.y ∈ (fullNodeToPolygon a c z).asIdeal ↔
      fullNodeQ a c ∈ z.asIdeal) := by
  change (algebraMap B N (NodalFiber.polygonNodeEquiv.symm
      PolygonNodeLocalization.x) ∈ z.asIdeal ↔ _) ∧
    (algebraMap B N (NodalFiber.polygonNodeEquiv.symm
      PolygonNodeLocalization.y) ∈ z.asIdeal ↔ _)
  rw [← NodalFiber.polygonNodeEquiv_p, ← NodalFiber.polygonNodeEquiv_q,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The full localized node has no smooth point at the intersection of its branches. -/
theorem fullNode_mem_smooth_iff (z : Spec (.of N)) :
    z ∈ (Spec.map (CommRingCat.ofHom (algebraMap K N))).smoothLocus ↔
      fullNodeP a c ∉ z.asIdeal ∨ fullNodeQ a c ∉ z.asIdeal := by
  have hs := PolygonAtlas.mem_smooth_iff (fullNodeToPolygon a c)
    (PolygonNodeBranches.toBase K) z
  simp only [fullNodeToPolygon_structure] at hs
  rw [← hs]
  change fullNodeToPolygon a c z ∈
    ((PolygonNodePresentation.aToBase K).smoothLocus : Set _) ↔ _
  rw [PolygonNodePresentation.a_smooth_complement,
    ← PolygonNodePresentation.a_zeroLocus_origin]
  change ¬ {PolygonNodeLocalization.x, PolygonNodeLocalization.y} ⊆
    ((fullNodeToPolygon a c z).asIdeal : Set A) ↔ _
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, not_and_or]
  exact or_congr (not_congr (fullNodeToPolygon_coordinates a c z).1)
    (not_congr (fullNodeToPolygon_coordinates a c z).2)

end FLT.Mazur.WeierstrassModificationX
