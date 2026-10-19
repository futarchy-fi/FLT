/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetTwoTorsion
public import FLT.Mazur.RationalPadicMinimalTransport
public import FLT.Mazur.EllipticPadicPrimeSemistability

/-!
# Minimal semistable local equations of actual Frey targets

A specified injective rational p-torsion map is transported through the
actual minimalizing variable change at every rational prime, including p.
Ellipticity follows from the target equation. No integrality of the canonical
Vélu equation at p is assumed.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur
open scoped WeierstrassCurve.Affine

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The entire original p-subgroup survives on an actual minimal semistable local equation. -/
theorem IsVeluTarget.exists_padic_minimal_semistable_model (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f)
    (q : ℕ) [Fact q.Prime] [DecidableEq ℚ_[q]] :
    let _ := h.isElliptic
    ∃ (W : WeierstrassCurve (padicIntegerSubring q)) (C : VariableChange ℚ_[q])
      (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
        W.map (algebraMap (padicIntegerSubring q) ℚ_[q])),
      IsMinimal (padicIntegerSubring q)
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      let g := (rationalPadicProjectiveHom q E W C hC).comp f
      Function.Injective g ∧ addOrderOf (g 1) = P.p ∧
      ((W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasGoodReduction
          (padicIntegerSubring q) ∨
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasMultiplicativeReduction
          (padicIntegerSubring q)) := by
  let _ := h.isElliptic
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨W, C, hC, hm, hi⟩ := exists_rational_padic_minimal_transport q E
  let _ := hm
  let _ : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic :=
    hC ▸ inferInstance
  let g := (rationalPadicProjectiveHom q E W C hC).comp f
  have hg : Function.Injective g := hi.comp hf
  have ho : addOrderOf (g 1) = P.p :=
    (addOrderOf_injective g hg 1).trans (ZMod.addOrderOf_one P.p)
  have hn : P.p • g 1 = 0 := by
    simpa only [ho] using addOrderOf_nsmul_eq_zero (g 1)
  have hne : g 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (hg (hz.trans (map_zero g).symm))
  exact ⟨W, C, hC, hm, hg, ho,
    padic_semistable_of_prime_torsion q W P.p hp17 (g 1) hne hn⟩

end FreyPackage
