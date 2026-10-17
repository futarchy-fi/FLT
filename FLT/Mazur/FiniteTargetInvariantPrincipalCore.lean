/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTargetNormCore
public import FLT.Mazur.RelativeRelationOrbitOpens

/-!
# Invariant affine cores of principal finite target domains

The domain before taking the norm need not be invariant. Reflexivity and
transitivity identify the resulting norm open with the whole-orbit core,
so its invariance is proved from the original equivalence operations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- A whole-orbit condition is unchanged on related original source points. -/
theorem wholeFiber_condition_iff (W : Set A.left) {x y : A.left} (h : Related p q x y) :
    (∀ z : D.left, p.left z = x → q.left z ∈ W) ↔
      (∀ z : D.left, p.left z = y → q.left z ∈ W) := by
  have step {a b : A.left} (hab : Related p q a b)
      (ha : ∀ z : D.left, p.left z = a → q.left z ∈ W) :
      ∀ z : D.left, p.left z = b → q.left z ∈ W := by
    intro z hz
    obtain ⟨w, hw, he⟩ := related_trans e hab ⟨z, hz, rfl⟩
    exact he ▸ ha w hw
  exact ⟨step h, step (related_symm e h)⟩

variable [IsAffine A.left] [Flat p.left] [LocallyOfFinitePresentation p.left]
  (s : Γ(A.left, ⊤)) (hs : A.left.basicOpen s ≤ finiteTargetOpen p.left)

/-- The affine whole-orbit core of a principal domain in the finite locus. -/
def finitePrincipalCore : A.left.Opens :=
  FiniteTargetNormCore.core p.left q.left
    ⟨A.left.basicOpen s, (isAffineOpen_top A.left).basicOpen s⟩ hs s

include e in
/-- The core tests every original arrow, with no invariance assumption on the input domain. -/
theorem mem_finitePrincipalCore_iff (x : A.left) :
    x ∈ finitePrincipalCore (q := q) s hs ↔
      ∀ z : D.left, p.left z = x → q.left z ∈ A.left.basicOpen s := by
  rw [finitePrincipalCore, FiniteTargetNormCore.mem_core_iff]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨z, hp, hq⟩ := related_refl e x
  exact hq ▸ h z hp

/-- Every principal core is affine as an open of the unchanged original source. -/
theorem finitePrincipalCore_isAffine : IsAffineOpen (finitePrincipalCore (q := q) s hs) :=
  FiniteTargetNormCore.core_isAffine _ _ _ _ _

/-- The constructed affine core is contained in the original principal neighborhood. -/
theorem finitePrincipalCore_le : finitePrincipalCore (q := q) s hs ≤ A.left.basicOpen s :=
  FiniteTargetNormCore.core_le _ _ _ _ _

include e in
/-- Equivalence operations prove saturation of the constructed affine core. -/
theorem finitePrincipalCore_preimage_eq :
    p.left ⁻¹ᵁ finitePrincipalCore (q := q) s hs =
      q.left ⁻¹ᵁ finitePrincipalCore (q := q) s hs := by
  ext z
  change p.left z ∈ finitePrincipalCore (q := q) s hs ↔ q.left z ∈ finitePrincipalCore (q := q) s hs
  rw [mem_finitePrincipalCore_iff e, mem_finitePrincipalCore_iff e]
  exact wholeFiber_condition_iff e _ ⟨z, rfl, rfl⟩

end FLT.Mazur.RelativeRelationOrbit
