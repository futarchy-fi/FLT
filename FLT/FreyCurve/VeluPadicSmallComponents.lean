/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluPadicMinimalModel
public import FLT.Mazur.EllipticPadicPrimeComponents
public import FLT.Mazur.EllipticCyclicComponentTransport

/-!
# Split components of actual Frey targets at two and three

The exact original rational torsion parameterization injects into the
component quotient of the constructed minimal model. Every nonzero parameter
has nonsmooth reduction, and p divides the positive minimal discriminant depth.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur IsLocalRing
open scoped WeierstrassCurve.Affine

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- At two and three, the specified rational subgroup injects into split components. -/
theorem IsVeluTarget.exists_padic_small_component_model (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f)
    (q : ℕ) [Fact q.Prime] [DecidableEq ℚ_[q]] (hq : q = 2 ∨ q = 3) :
    let _ := h.isElliptic
    ∃ (W : WeierstrassCurve (padicIntegerSubring q)) (C : VariableChange ℚ_[q])
      (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
        W.map (algebraMap (padicIntegerSubring q) ℚ_[q])),
      IsMinimal (padicIntegerSubring q)
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      let g := (rationalPadicProjectiveHom q E W C hC).comp f
      Function.Injective g ∧
      (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasMultiplicativeReduction
        (padicIntegerSubring q) ∧
      (W.nodePoly.map (residue (padicIntegerSubring q))).Splits ∧
      Function.Injective ((ellipticComponentHom (padicIntegerSubring q) W).comp g) ∧
      (∀ a, SmoothReduction (padicIntegerSubring q) W (g a) ↔ a = 0) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring q) ^ n ∧
        W.Δ ∉ maximalIdeal (padicIntegerSubring q) ^ (n + 1) ∧ P.p ∣ n := by
  let _ := h.isElliptic
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨W, C, hC, hm, hg, ho, _⟩ :=
    h.exists_padic_minimal_semistable_model hp17 f hf q
  let _ := hm
  let _ : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic :=
    hC ▸ inferInstance
  let g := (rationalPadicProjectiveHom q E W C hC).comp f
  change addOrderOf (g 1) = P.p at ho
  have hn : P.p • g 1 = 0 := by
    simpa only [ho] using addOrderOf_nsmul_eq_zero (g 1)
  have hne : g 1 ≠ 0 := by
    intro hz
    rw [hz, addOrderOf_zero] at ho
    omega
  obtain ⟨hmul, hs, hsplit, _, hd⟩ :=
    padic_prime_torsion_components_small q hq W P.p hp17 (g 1) hne hn
  exact ⟨W, C, hC, hm, hg, hmul, hsplit,
    cyclicComponentHom_injective _ W P.p g hs,
    cyclic_smoothReduction_iff _ W P.p g hs, hd⟩

end FreyPackage
