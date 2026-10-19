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
# The actual Frey target at the kernel prime

Minimalization supplies an integral equation at p even when the canonical
Vélu coefficients are not integral there. In its bad-reduction branch, the
retained rational p-subgroup injects into split components and p divides the
positive minimal discriminant depth. The good-reduction branch remains open.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur IsLocalRing
open scoped WeierstrassCurve.Affine

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- Construct the minimal model at p and its exact cyclic component map in the bad branch. -/
theorem IsVeluTarget.exists_padic_prime_component_model (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let _ : Fact P.p.Prime := ⟨P.pp⟩
    let _ := Classical.decEq ℚ_[P.p]
    let _ := h.isElliptic
    ∃ (W : WeierstrassCurve (padicIntegerSubring P.p)) (C : VariableChange ℚ_[P.p])
      (hC : C • E.map (algebraMap ℚ ℚ_[P.p]) =
        W.map (algebraMap (padicIntegerSubring P.p) ℚ_[P.p])),
      IsMinimal (padicIntegerSubring P.p)
        (W.map (algebraMap (padicIntegerSubring P.p) ℚ_[P.p])) ∧
      let g := (rationalPadicProjectiveHom P.p E W C hC).comp f
      Function.Injective g ∧ addOrderOf (g 1) = P.p ∧
      ((W.map (algebraMap (padicIntegerSubring P.p) ℚ_[P.p])).HasGoodReduction
          (padicIntegerSubring P.p) ∨
        (W.map (algebraMap (padicIntegerSubring P.p) ℚ_[P.p])).HasMultiplicativeReduction
          (padicIntegerSubring P.p)) ∧
      (W.Δ ∈ maximalIdeal (padicIntegerSubring P.p) →
        IsUnit W.c₄ ∧ (W.nodePoly.map (residue (padicIntegerSubring P.p))).Splits ∧
        Function.Injective ((ellipticComponentHom (padicIntegerSubring P.p) W).comp g) ∧
        (∀ a, SmoothReduction (padicIntegerSubring P.p) W (g a) ↔ a = 0) ∧
        ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring P.p) ^ n ∧
          W.Δ ∉ maximalIdeal (padicIntegerSubring P.p) ^ (n + 1) ∧ P.p ∣ n) := by
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  let _ := Classical.decEq ℚ_[P.p]
  let _ := h.isElliptic
  obtain ⟨W, C, hC, hm, hg, ho, hss⟩ :=
    h.exists_padic_minimal_semistable_model hp17 f hf P.p
  let _ := hm
  let _ : (W.map (algebraMap (padicIntegerSubring P.p) ℚ_[P.p])).IsElliptic :=
    hC ▸ inferInstance
  let g := (rationalPadicProjectiveHom P.p E W C hC).comp f
  change addOrderOf (g 1) = P.p at ho
  have hn : P.p • g 1 = 0 := by
    simpa only [ho] using addOrderOf_nsmul_eq_zero (g 1)
  have hne : g 1 ≠ 0 := by
    intro hz
    rw [hz, addOrderOf_zero] at ho
    omega
  refine ⟨W, C, hC, hm, hg, ho, hss, ?_⟩
  intro hd
  obtain ⟨hu, hs, hsplit, _, hn⟩ :=
    padic_prime_torsion_components_at_prime P.p hp17 W hd (g 1) hne hn
  exact ⟨hu, hsplit, cyclicComponentHom_injective _ W P.p g hs,
    cyclic_smoothReduction_iff _ W P.p g hs, hn⟩

end FreyPackage
