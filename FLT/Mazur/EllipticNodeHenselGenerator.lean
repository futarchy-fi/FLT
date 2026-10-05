/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentGenerator
public import FLT.Mazur.EllipticNodeGenericNonsingular
public import FLT.Mazur.EllipticNodeHenselCoordinates

/-!
# The split nodal component group over a Henselian valuation ring

The depth-one coordinates give an actual point of label one, including the
midpoint at depth two. Depth one itself has trivial target. Thus the canonical
component map is an additive equivalence with Z/nZ; completeness at the
maximal ideal is a sufficient hypothesis through the Henselian instance.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) [HenselianRing A (maximalIdeal A)]

/-- Hensel lifting constructs an actual generic point of label one at every positive depth. -/
theorem exists_nodePointLabel_one :
    ∃ P : (W.map (algebraMap A K)).toProjective.Point, nodePointLabel D P = 1 := by
  by_cases hn₁ : n = 1
  · subst n
    exact ⟨0, by rw [nodePointLabel_zero]; exact Subsingleton.elim _ _⟩
  by_cases hn₂ : n = 2
  · subst n
    obtain ⟨a, ha⟩ := exists_node_middle_hensel_coordinates D
    have he : W.toAffine.Equation (π ^ 1 * a) (π ^ 1 * 1) := by simpa using ha
    let P := Affine.Point.toProjective (.some _ _ (D.generic_nonsingular he))
    let v : NodePointCoordinates A W π P :=
      ⟨1, a, 1, Or.inr isUnit_one, D.generic_nonsingular he, rfl⟩
    refine ⟨P, ?_⟩
    rw [nodePointLabel_eq_of_coordinates D v]
    exact (nodeBranchLabel_middle (R := A) (by decide : 2 * 1 = 2) 1).1
  · obtain ⟨b, hb, he⟩ := exists_node_first_hensel_coordinates D (by have := D.depth_pos; omega)
    have he' : W.toAffine.Equation (π ^ 1 * 1) (π ^ 1 * b) := by simpa using he
    let P := Affine.Point.toProjective (.some _ _ (D.generic_nonsingular he'))
    let v : NodePointCoordinates A W π P :=
      ⟨1, 1, b, Or.inl isUnit_one, D.generic_nonsingular he', rfl⟩
    refine ⟨P, ?_⟩
    rw [nodePointLabel_eq_of_coordinates D v]
    simpa only [Nat.cast_one] using nodeBranchLabel_of_mem n 1 hb

/-- Every split nodal label is attained over a Henselian valuation ring. -/
theorem nodePointLabel_surjective_of_henselian : Function.Surjective (nodePointLabel D) := by
  obtain ⟨P, hP⟩ := exists_nodePointLabel_one D
  exact nodePointLabel_surjective_of_one D P hP

/-- The canonical component label is surjective over a Henselian valuation ring. -/
theorem nodeComponentLabelHom_surjective_of_henselian :
    Function.Surjective (nodeComponentLabelHom D) := by
  obtain ⟨P, hP⟩ := exists_nodePointLabel_one D
  exact nodeComponentLabelHom_surjective_of_one D P hP

/-- The split nodal component quotient is canonically Z/nZ. -/
noncomputable def nodeComponentLabelEquiv : EllipticComponentQuotient A W ≃+ ZMod n :=
  AddEquiv.ofBijective (nodeComponentLabelHom D)
    ⟨nodeComponentLabelHom_injective D, nodeComponentLabelHom_surjective_of_henselian D⟩

/-- The Henselian equivalence is the existing canonical component label. -/
@[simp] theorem nodeComponentLabelEquiv_apply (c : EllipticComponentQuotient A W) :
    nodeComponentLabelEquiv D c = nodeComponentLabel D c := rfl

include D in
/-- Exact nodal depth equals the number of components over a Henselian valuation ring. -/
theorem natCard_ellipticComponentQuotient_eq_of_henselian :
    Nat.card (EllipticComponentQuotient A W) = n := by
  simpa only [Nat.card_zmod] using Nat.card_congr (nodeComponentLabelEquiv D).toEquiv

end FLT.Mazur
