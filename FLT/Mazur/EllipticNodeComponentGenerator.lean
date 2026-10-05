/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentCyclic

/-!
# A single lifted label gives the full split component group

Once a generic point of label one is constructed, its multiples lift every
label. The already injective component map is then an additive equivalence
with Z/nZ and the component quotient has exact order n. Constructing that
point from completeness is a separate lifting obligation.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  (P : (W.map (algebraMap A K)).toProjective.Point) (hP : nodePointLabel D P = 1)

include hP

/-- Multiples of a point of label one lift every residue label. -/
theorem nodePointLabel_surjective_of_one : Function.Surjective (nodePointLabel D) := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  intro c
  refine ⟨c.val • P, ?_⟩
  change nodePointLabelHom D (c.val • P) = c
  rw [map_nsmul, nodePointLabelHom_apply, hP, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- A lifted generator makes the canonical component map surjective. -/
theorem nodeComponentLabelHom_surjective_of_one :
    Function.Surjective (nodeComponentLabelHom D) := by
  intro c
  obtain ⟨Q, hQ⟩ := nodePointLabel_surjective_of_one D P hP c
  exact ⟨ellipticComponentHom A W Q, hQ⟩

/-- The canonical additive equivalence supplied by an actual point of label one. -/
noncomputable def nodeComponentLabelEquivOfOne : EllipticComponentQuotient A W ≃+ ZMod n :=
  AddEquiv.ofBijective (nodeComponentLabelHom D)
    ⟨nodeComponentLabelHom_injective D, nodeComponentLabelHom_surjective_of_one D P hP⟩

/-- The equivalence uses the canonical component label on every class. -/
@[simp] theorem nodeComponentLabelEquivOfOne_apply (c : EllipticComponentQuotient A W) :
    nodeComponentLabelEquivOfOne D P hP c = nodeComponentLabel D c := rfl

/-- A lifted label one proves that the actual component quotient has exact order n. -/
theorem natCard_ellipticComponentQuotient_eq_of_label_one :
    Nat.card (EllipticComponentQuotient A W) = n := by
  simpa only [Nat.card_zmod] using Nat.card_congr (nodeComponentLabelEquivOfOne D P hP).toEquiv

end FLT.Mazur
