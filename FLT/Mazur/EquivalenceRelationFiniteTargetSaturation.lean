/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiniteFiberLocus
public import FLT.Mazur.SchemeFiniteTargetFppfBaseChange

/-!
# The original finite target locus is invariant under the whole relation

Rebasing identifies the entire pullbacks over the two endpoints. Flat locally
presented descent then identifies their finite loci with inverse images of
the original finite locus. This proves saturation without assuming it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationFiber
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  [IsSeparated p] [LocallyQuasiFinite p] [Flat p] [LocallyOfFinitePresentation p]
  [Flat q] [LocallyOfFinitePresentation q]

include e in
/-- The entire original finite target locus is saturated under original arrows. -/
theorem finiteTargetOpen_preimage_eq :
    p ⁻¹ᵁ finiteTargetOpen p = q ⁻¹ᵁ finiteTargetOpen p := by
  have h := rebase_finiteTargetOpen e (𝟙 D)
  rw [Category.id_comp, Category.id_comp] at h
  rwa [finiteTargetOpen_fppf_baseChange (IsPullback.of_hasPullback p p),
    finiteTargetOpen_fppf_baseChange (IsPullback.of_hasPullback p q)] at h

include e in
/-- An original arrow transports actual finite neighborhoods in both directions. -/
theorem finiteTargetOpen_endpoints_iff (z : D) :
    p z ∈ finiteTargetOpen p ↔ q z ∈ finiteTargetOpen p := by
  change z ∈ p ⁻¹ᵁ finiteTargetOpen p ↔ z ∈ q ⁻¹ᵁ finiteTargetOpen p
  rw [finiteTargetOpen_preimage_eq e]

include e in
/-- Entire first-endpoint fibers over the finite locus also lie over it at the other endpoint. -/
theorem finiteTargetOpen_fullFiber (x : A) (hx : x ∈ finiteTargetOpen p) :
    ∀ z : D, p z = x → q z ∈ finiteTargetOpen p := by
  intro z hz
  exact (finiteTargetOpen_endpoints_iff e z).mp (hz.symm ▸ hx)

end FLT.Mazur.EquivalenceRelationFiber
