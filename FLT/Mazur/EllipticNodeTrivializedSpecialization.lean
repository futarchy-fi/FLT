/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterTrivialization
public import FLT.Mazur.EllipticResolvedParameterEquality
public import FLT.Mazur.EllipticResolvedAdditionCongruence

/-!
# Product coordinates detect the actual resolved specialization

A specified period root gives a homomorphism into the split product of the
label group and residue units. Its equality relation is exactly equality
in the actual resolved smooth fiber, and its kernel is the original E₁.
No surjectivity onto residue points or scheme comparison is asserted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing WeierstrassDividedDepth
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
  (hr : r ^ n = nodeWrapParameterUnit D c₆ h6)

/-- The original label and trivialized parameter form an actual additive homomorphism. -/
def nodeTrivializedSpecialization :
    (W.map (algebraMap A K)).toProjective.Point →+ ZMod n × Additive (ResidueField A)ˣ :=
  (nodePointLabelHom D).prod (nodeTrivializedParameterHom D c₆ h6 r hr)

/-- The first product coordinate is the original proved component label. -/
@[simp] theorem nodeTrivializedSpecialization_fst
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    (nodeTrivializedSpecialization D c₆ h6 r hr P).1 = nodePointLabel D P := rfl

/-- The second coordinate is the explicitly trivialized original parameter. -/
@[simp] theorem nodeTrivializedSpecialization_snd
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    (nodeTrivializedSpecialization D c₆ h6 r hr P).2 =
      Additive.ofMul (nodeTrivializedParameter D c₆ h6 r P) := rfl

/-- Product coordinates agree exactly when the original labels and parameters agree. -/
theorem nodeTrivializedSpecialization_eq_iff_coordinates
    {P Q : (W.map (algebraMap A K)).toProjective.Point} :
    nodeTrivializedSpecialization D c₆ h6 r hr P =
      nodeTrivializedSpecialization D c₆ h6 r hr Q ↔
        nodePointLabel D P = nodePointLabel D Q ∧
          nodePointParameter D c₆ P = nodePointParameter D c₆ Q := by
  constructor
  · intro he
    have hl := congrArg Prod.fst he
    change nodePointLabel D P = nodePointLabel D Q at hl
    refine ⟨hl, (nodeTrivializedParameter_eq_iff D c₆ h6 r hl).mp ?_⟩
    exact congrArg (fun x => Additive.toMul x.2) he
  · rintro ⟨hl, hz⟩
    apply Prod.ext hl
    exact congrArg Additive.ofMul ((nodeTrivializedParameter_eq_iff D c₆ h6 r hl).mpr hz)

/-- The split product coordinates detect equality of actual resolved smooth points. -/
theorem nodeTrivializedSpecialization_eq_iff_resolved
    {P Q : (W.map (algebraMap A K)).toProjective.Point} :
    nodeTrivializedSpecialization D c₆ h6 r hr P =
      nodeTrivializedSpecialization D c₆ h6 r hr Q ↔
        resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q := by
  rw [nodeTrivializedSpecialization_eq_iff_coordinates,
    resolvedSplitSmoothPoint_eq_iff_label_parameter A D c₆ h6]

/-- The split product homomorphism has exactly the original infinity-reduction kernel. -/
theorem nodeTrivializedSpecialization_eq_zero_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodeTrivializedSpecialization D c₆ h6 r hr P = 0 ↔ InfinityReduction A W P := by
  rw [← map_zero (nodeTrivializedSpecialization D c₆ h6 r hr),
    nodeTrivializedSpecialization_eq_iff_resolved,
    resolvedSplitSmoothPoint_eq_iff_difference A D, sub_zero]

/-- The exact kernel is E₁, with no component or original E₀ restriction. -/
theorem nodeTrivializedSpecialization_ker :
    (nodeTrivializedSpecialization D c₆ h6 r hr).ker = ellipticE1 A W := by
  ext P
  exact nodeTrivializedSpecialization_eq_zero_iff D c₆ h6 r hr P

end FLT.Mazur
