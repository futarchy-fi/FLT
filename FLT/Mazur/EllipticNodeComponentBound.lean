/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelDescent
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Canonical component labels and the split component bound

The nodal label descends to an injective function from the actual E/E₀ to
Z/nZ, so the component quotient is finite of cardinality at most n. The map
preserves zero and negation; additivity for two singular points is still open.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

/-- The canonical label of an actual component class, as a function. -/
noncomputable def nodeComponentLabel : EllipticComponentQuotient A W → ZMod n :=
  Quotient.lift (nodePointLabel D) (fun _ _ h =>
    (ellipticComponentHom_eq_iff_nodePointLabel_eq D).mp (Quotient.sound h))

/-- The descended function recovers the label of every representative. -/
@[simp] theorem nodeComponentLabel_mk (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodeComponentLabel D (ellipticComponentHom A W P) = nodePointLabel D P := rfl

/-- The canonical component label is injective. -/
theorem nodeComponentLabel_injective : Function.Injective (nodeComponentLabel D) := by
  intro c d h
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  exact (ellipticComponentHom_eq_iff_nodePointLabel_eq D).mpr h

/-- The identity component has label zero. -/
@[simp] theorem nodeComponentLabel_zero : nodeComponentLabel D 0 = 0 := by
  rw [← map_zero (ellipticComponentHom A W), nodeComponentLabel_mk, nodePointLabel_zero]

/-- Negation of actual component classes negates their labels. -/
@[simp] theorem nodeComponentLabel_neg (c : EllipticComponentQuotient A W) :
    nodeComponentLabel D (-c) = -nodeComponentLabel D c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  rw [← map_neg, nodeComponentLabel_mk, nodeComponentLabel_mk, nodePointLabel_neg]

include D

/-- The actual quotient by nonsingular reduction is finite for a deep split model. -/
theorem finite_ellipticComponentQuotient_of_splitNodeDepth :
    Finite (EllipticComponentQuotient A W) := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  exact Finite.of_injective _ (nodeComponentLabel_injective D)

/-- The number of actual rational component classes is at most the split depth. -/
theorem natCard_ellipticComponentQuotient_le_splitNodeDepth :
    Nat.card (EllipticComponentQuotient A W) ≤ n := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective _ (nodeComponentLabel_injective D)

/-- Translation by any point of E₀ preserves the label, including the infinity chart. -/
theorem nodePointLabel_add_smooth_right
    (P Q : (W.map (algebraMap A K)).toProjective.Point) (hQ : SmoothReduction A W Q) :
    nodePointLabel D (P + Q) = nodePointLabel D P := by
  apply (ellipticComponentHom_eq_iff_nodePointLabel_eq D).mp
  rw [map_add, (ellipticComponentHom_eq_zero A W Q).mpr hQ, add_zero]

/-- The label addition law whenever either summand has smooth reduction. -/
theorem nodePointLabel_add_of_smooth
    (P Q : (W.map (algebraMap A K)).toProjective.Point)
    (h : SmoothReduction A W P ∨ SmoothReduction A W Q) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  rcases h with hp | hq
  · rw [add_comm P Q, nodePointLabel_add_smooth_right D Q P hp,
      (nodePointLabel_eq_zero_iff D P).mpr hp, zero_add]
  · rw [nodePointLabel_add_smooth_right D P Q hq, (nodePointLabel_eq_zero_iff D Q).mpr hq, add_zero]

end FLT.Mazur
