/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteEndpointOrbit
public import FLT.Mazur.EquivalenceRelationCompletePointLocus

/-!
# Complete stable charts have saturated original images

The image of a complete stable normalized chart is an actual original source open
invariant under the entire original relation. Point lifting uses a scheme pullback;
no preservation of fiber products by the underlying-point functor is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U)
  (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)

/-- The actual open image of the normalized chart in the unchanged original source. -/
def completeChartImage : A.Opens := by
  let _ := first_etale e I o
  exact ⟨Set.range (U.ι ≫ first p q I o),
    (U.ι ≫ first p q I o).isOpenMap.isOpen_range⟩

include hc hU in
/-- Every original arrow starting in the chart image also ends in that same image. -/
theorem completeChartImage_target (a : D) (ha : p a ∈ completeChartImage e I o U) :
    q a ∈ completeChartImage e I o U := by
  obtain ⟨x, hx⟩ := ha
  let π := U.ι ≫ first p q I o
  obtain ⟨w, _, hw'⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback π p) x a hx
  let b := (pullback π p).fromSpecResidueField w
  let u := b ≫ pullback.fst π p ≫ U.ι
  let v := b ≫ pullback.snd π p
  have hu : Complete I o u := by
    rw [complete_iff_mem_completePointLocus]
    exact hc (pullback.fst π p (b default)).property
  have hv : v ≫ p = u ≫ first p q I o := by
    dsimp only [v, u, π]
    simp only [Category.assoc, pullback.condition]
  obtain ⟨σ, hσ⟩ := complete_arrow_endpoint_permutation e I o u hu v hv
  have hy : (action e I o σ).hom (u default) ∈ U := by
    have he := congrArg (fun W : (source p q I o).Opens ↦ u default ∈ W) (hU σ)
    exact he.to_iff.mpr (pullback.fst π p (b default)).property
  refine ⟨⟨(action e I o σ).hom (u default), hy⟩, ?_⟩
  change (u ≫ (action e I o σ).hom ≫ first p q I o) default = q a
  rw [hσ]
  change q (pullback.snd π p (b default)) = q a
  rw [Scheme.fromSpecResidueField_apply, hw']

include hc hU in
/-- The constructed open image is saturated for both endpoints of the full original relation. -/
theorem completeChartImage_invariant :
    p ⁻¹ᵁ completeChartImage e I o U = q ⁻¹ᵁ completeChartImage e I o U := by
  apply TopologicalSpace.Opens.ext
  ext a
  constructor
  · exact completeChartImage_target e I o U hU hc a
  · intro ha
    have hp : p (e.s a) = q a := congrArg (fun f ↦ f a) e.symmetry₁
    have hq : q (e.s a) = p a := congrArg (fun f ↦ f a) e.symmetry₂
    have h := completeChartImage_target e I o U hU hc (e.s a) (hp.symm ▸ ha)
    change p a ∈ completeChartImage e I o U
    rwa [hq] at h

end FLT.Mazur.EquivalenceRelationNormalizedFrames
