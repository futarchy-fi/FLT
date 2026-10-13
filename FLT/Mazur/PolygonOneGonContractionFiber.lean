/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionTorus

/-!
# The collapsed fiber of the original polygon contraction

The target node defines an actual closed fiber. Its ideal vanishes on every
omitted complete component and every original node. On the retained component
it is precisely the original one-gon normalization fiber ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

instance targetNode_closed : IsClosedImmersion (targetNode K).left := by
  change IsClosedImmersion ((nodeι K 1 0).left ≫ (PolygonAtlas.nodes K 1).left)
  infer_instance

/-- The node pulls its own ideal back to zero, with its scheme structure retained. -/
theorem targetNode_ideal_self : (targetNode K).left.ker.comap (targetNode K).left = ⊥ := by
  have H := IsKernelPair.id_of_mono (targetNode K).left
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- The sole target node is exactly the complement of the full target Laurent chart. -/
theorem targetNode_range :
    Set.range (targetNode K).left = (Set.range (PolygonAtlas.torus K 1 0).left)ᶜ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact targetNode_not_torus K z
  · intro hx
    have hs : x ∉ (PolygonAtlas.polygon K 1).hom.smoothLocus := by
      change x ∉ ((PolygonAtlas.polygon K 1).hom.smoothLocus : Set _)
      rw [PolygonAtlas.smooth_range]
      simpa only [Set.mem_iUnion, Fin.exists_fin_one, Set.mem_compl_iff] using hx
    obtain ⟨j, z, hz⟩ := PolygonNodeLocus.atlas_nonsmooth_cover K 1 x hs
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ⟨z, hz⟩

variable (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The actual ideal sheaf defining the full collapsed fiber. -/
def fiberIdeal : C.left.IdealSheafData :=
  (targetNode K).left.ker.comap (contraction K n hn p q h i).left

/-- The full collapsed fiber has exactly the complement of the retained Laurent open as support. -/
theorem fiberIdeal_support :
    ((fiberIdeal K n hn p q h i).support : Set C.left) =
      (Set.range (torusToComponent K ≫ componentι K n i ≫ p).left)ᶜ := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let _ := torus_isOpenImmersion K n hn p q h i
  have he := contraction_torus_preimage K n hn p q h i
  rw [fiberIdeal, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker]
  rw [(targetNode K).left.isClosedMap.isClosed_range.closure_eq, targetNode_range]
  ext x
  exact not_congr (SetLike.ext_iff.mp he x)

/-- On an omitted component, the fiber is the entire original projective line as a scheme. -/
theorem fiberIdeal_omitted {j : Fin n} (hj : j ≠ i) :
    (fiberIdeal K n hn p q h i).comap (componentι K n j ≫ p).left = ⊥ := by
  rw [fiberIdeal, ← Scheme.IdealSheafData.comap_comp]
  change (targetNode K).left.ker.comap
    (componentι K n j ≫ p ≫ contraction K n hn p q h i).left = _
  rw [omitted_contraction K n hn p q h i hj]
  change (targetNode K).left.ker.comap ((componentToPoint K).left ≫ (targetNode K).left) = _
  rw [Scheme.IdealSheafData.comap_comp, targetNode_ideal_self,
    Scheme.IdealSheafData.comap_bot]

/-- Every original pinching node lies scheme-theoretically in the collapsed fiber. -/
theorem fiberIdeal_node (j : Fin n) :
    (fiberIdeal K n hn p q h i).comap (nodeι K n j ≫ q).left = ⊥ := by
  rw [fiberIdeal, ← Scheme.IdealSheafData.comap_comp]
  change (targetNode K).left.ker.comap
    (nodeι K n j ≫ q ≫ contraction K n hn p q h i).left = _
  rw [node_contraction, targetNode_ideal_self]

/-- The retained component has the exact original normalization fiber ideal. -/
theorem fiberIdeal_retained :
    (fiberIdeal K n hn p q h i).comap (componentι K n i ≫ p).left =
      (targetNode K).left.ker.comap (retainedComponent K).left := by
  rw [fiberIdeal, ← Scheme.IdealSheafData.comap_comp]
  change (targetNode K).left.ker.comap
    (componentι K n i ≫ p ≫ contraction K n hn p q h i).left = _
  rw [retained_contraction]

/-- Every omitted complete component maps canonically to the actual closed fiber. -/
def omittedFiberMap {j : Fin n} (hj : j ≠ i) :
    (component K).left ⟶
      pullback (contraction K n hn p q h i).left (targetNode K).left :=
  pullback.lift (componentι K n j ≫ p).left (componentToPoint K).left
    (congrArg Over.Hom.left (omitted_contraction K n hn p q h i hj))

/-- The closed-fiber lift keeps the original complete normalization component. -/
@[reassoc] theorem omittedFiberMap_fst {j : Fin n} (hj : j ≠ i) :
    omittedFiberMap K n hn p q h i hj ≫ pullback.fst _ _ = (componentι K n j ≫ p).left :=
  pullback.lift_fst _ _ _

/-- The fiber lift uses precisely the original coefficient point. -/
@[reassoc] theorem omittedFiberMap_snd {j : Fin n} (hj : j ≠ i) :
    omittedFiberMap K n hn p q h i hj ≫ pullback.snd _ _ = (componentToPoint K).left :=
  pullback.lift_snd _ _ _

end FLT.Mazur.PolygonOneGonContraction
