/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluPadicTwoMinimal
public import FLT.FreyCurve.VeluPadicSmallComponents

/-!
# Components on the canonical Frey target at two

At two, a₁ = 1 already makes the canonical integral equation minimal.
Consequently the original rational subgroup injects into its split components
using the identity variable change. The positive p-divisible discriminant
depth belongs to this very equation, not an unspecified isomorphic model.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur IsLocalRing
open scoped WeierstrassCurve.Affine

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The canonical target at two has split components carrying the original p-subgroup. -/
theorem IsVeluTarget.exists_canonical_two_component_model (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let _ := h.isElliptic
    let _ := Classical.decEq ℚ_[2]
    ∃ (W : WeierstrassCurve (padicIntegerSubring 2))
      (hW : (1 : VariableChange ℚ_[2]) • E.map (algebraMap ℚ ℚ_[2]) =
        W.map (algebraMap (padicIntegerSubring 2) ℚ_[2])),
      W.map (algebraMap (padicIntegerSubring 2) ℚ_[2]) = E.map (algebraMap ℚ ℚ_[2]) ∧
      IsUnit W.c₄ ∧
      (E.map (algebraMap ℚ ℚ_[2])).HasMultiplicativeReduction (padicIntegerSubring 2) ∧
      (W.nodePoly.map (residue (padicIntegerSubring 2))).Splits ∧
      let g := (rationalPadicProjectiveHom 2 E W 1 hW).comp f
      Function.Injective ((ellipticComponentHom (padicIntegerSubring 2) W).comp g) ∧
      (∀ a, SmoothReduction (padicIntegerSubring 2) W (g a) ↔ a = 0) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring 2) ^ n ∧
        W.Δ ∉ maximalIdeal (padicIntegerSubring 2) ^ (n + 1) ∧ P.p ∣ n := by
  let _ := h.isElliptic
  let _ := Classical.decEq ℚ_[2]
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨W, hw, hc⟩ := h.exists_padic_two_unit_model
  have hW : (1 : VariableChange ℚ_[2]) • E.map (algebraMap ℚ ℚ_[2]) =
      W.map (algebraMap (padicIntegerSubring 2) ℚ_[2]) := by rw [one_smul, hw]
  let _ : (W.map (algebraMap (padicIntegerSubring 2) ℚ_[2])).IsElliptic :=
    hw.symm ▸ inferInstance
  let _ : IsMinimal (padicIntegerSubring 2)
      (W.map (algebraMap (padicIntegerSubring 2) ℚ_[2])) := hw.symm ▸ h.padic_two_isMinimal
  let g := (rationalPadicProjectiveHom 2 E W 1 hW).comp f
  have hg : Function.Injective g :=
    (rationalPadicProjectiveHom_injective 2 E W 1 hW).comp hf
  have ho : addOrderOf (g 1) = P.p :=
    (addOrderOf_injective g hg 1).trans (ZMod.addOrderOf_one P.p)
  have hn : P.p • g 1 = 0 := by
    simpa only [ho] using addOrderOf_nsmul_eq_zero (g 1)
  have hne : g 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (hg (hz.trans (map_zero g).symm))
  obtain ⟨hm, hs, hsplit, _, hd⟩ :=
    padic_prime_torsion_components_small 2 (Or.inl rfl) W P.p hp17 (g 1) hne hn
  exact ⟨W, hW, hw, hc, hw ▸ hm, hsplit,
    cyclicComponentHom_injective _ W P.p g hs,
    cyclic_smoothReduction_iff _ W P.p g hs, hd⟩

end FreyPackage
