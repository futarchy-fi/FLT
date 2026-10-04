/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteParameterCarry

/-!
# Changing rational coordinates of a parameter carry

Equal rational-circle characters give cohomologous carries. The bounding
cochain is the integer difference of the chosen rational representatives.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

variable {G : Type} [Group G] {n d : ℕ} [NeZero n] [NeZero d]
  (χ : G →* Multiplicative (ZMod n)) (ψ : G →* Multiplicative (ZMod d))
  (m : ℕ)

/-- Equal circle characters lift to integer differences of rational sections. -/
theorem parameterCarry_integer_difference
    (h : ∀ g, zmodToRatCircle n (χ g).toAdd = m • zmodToRatCircle d (ψ g).toAdd) :
    ∃ b : G → ℤ, ∀ g, (b g : ℚ) =
      ((χ g).toAdd.val : ℚ) / n - m * (((ψ g).toAdd.val : ℚ) / d) := by
  have hb (g : G) : ∃ z : ℤ, (z : ℚ) =
      ((χ g).toAdd.val : ℚ) / n - m * (((ψ g).toAdd.val : ℚ) / d) := by
    have hz := sub_eq_zero.mpr (h g)
    rw [zmodToRatCircle_apply, zmodToRatCircle_apply,
      ← AddCircle.coe_nsmul, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at hz
    simpa only [zsmul_eq_mul, mul_one, nsmul_eq_mul] using hz
  exact ⟨fun g => (hb g).choose, fun g => (hb g).choose_spec⟩

/-- The integer difference has the difference of the two carry differentials. -/
theorem parameterCarry_integer_boundary (b : G → ℤ)
    (hb : ∀ g, (b g : ℚ) =
      ((χ g).toAdd.val : ℚ) / n - m * (((ψ g).toAdd.val : ℚ) / d)) (g h : G) :
    b h - b (g * h) + b g =
      cyclicCarry (χ g).toAdd (χ h).toAdd - m * cyclicCarry (ψ g).toAdd (ψ h).toAdd := by
  have hn := cyclicCarry_rat (χ g).toAdd (χ h).toAdd
  have hd := cyclicCarry_rat (ψ g).toAdd (ψ h).toAdd
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hb, hb, hb]
  simp only [map_mul, toAdd_mul] at *
  rw [hn, hd]
  ring

variable [TopologicalSpace G] [DiscreteTopology G] [IsTopologicalGroup G] [Finite G]
  (M : Type) [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

local notation "V" => Rep.of (Representation.ofDistribMulAction ℤ G M)

/-- Rational character comparison induces the corresponding equality of actual H² classes. -/
theorem finiteParameterCarryClass_character_multiple (x : (V).ρ.invariants)
    (h : ∀ g, zmodToRatCircle n (χ g).toAdd = m • zmodToRatCircle d (ψ g).toAdd) :
    finiteParameterCarryClass χ M x = m • finiteParameterCarryClass ψ M x := by
  obtain ⟨b, hb⟩ := parameterCarry_integer_difference χ ψ m h
  let c : continuousTwoCocycles (G := G) (M := M) :=
    ⟨cyclicParameterCarry (finiteScalarCharacter ψ) x.val,
      cyclicParameterCarry_isCocycle _ _ x.property⟩
  change _ = m • integralH2ClassHom c
  rw [← map_nsmul]
  apply (integralH2Class_eq_iff _ (m • c).val _ (m • c).property).mpr
  refine ⟨⟨fun g => b g • x.val, continuous_of_discreteTopology⟩, fun g h => ?_⟩
  change g • (b h • x.val) - b (g * h) • x.val + b g • x.val =
    cyclicCarry (χ g).toAdd (χ h).toAdd • x.val -
      m • (cyclicCarry (ψ g).toAdd (ψ h).toAdd • x.val)
  have hx : g • x.val = x.val := x.property g
  rw [smul_comm g, hx, ← sub_smul, ← add_smul,
    parameterCarry_integer_boundary χ ψ m b hb]
  simp only [sub_smul, mul_smul, Nat.cast_smul_eq_nsmul]

end LocalClassFieldTheory
