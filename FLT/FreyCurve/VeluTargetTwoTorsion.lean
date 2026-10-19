/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetWitness
public import FLT.FreyCurve.Serre.QuotientCoordinateHom
public import FLT.FreyCurve.Serre.FreyTwoTorsion
public import FLT.FreyCurve.Serre.JoinCoprimeTorsion

/-!
# Full two-torsion on the actual Frey quotient targets

The target equation supplies ellipticity and an odd-kernel rational map.
Consequently full two-torsion is a theorem about these targets, not an extra
assumption of the eventual torsion exclusion.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- Every allowed target is elliptic by its equation. -/
theorem IsVeluTarget.isElliptic (h : P.IsVeluTarget E) : E.IsElliptic := by
  rcases h with rfl | ⟨q, _, _, heq⟩
  · infer_instance
  · exact heq.isElliptic P.freyCurve P.p P.hppos q P.hp_odd

/-- Every allowed target receives the constructed rational map with p-killed kernel. -/
theorem IsVeluTarget.exists_rational_map (h : P.IsVeluTarget E) :
    ∃ φ : (P.freyCurve⁄ℚ).Point →+ (E⁄ℚ).Point,
      ∀ a, φ a = 0 → P.p • a = 0 := by
  rcases h with rfl | ⟨q, hq, hfixed, heq⟩
  · refine ⟨AddMonoidHom.id _, ?_⟩
    intro a ha
    change a = 0 at ha
    rw [ha, nsmul_zero]
  · obtain ⟨φ, _, hφ, _⟩ := Velu.rational_maps_of_torsionQuotientEquation
      P.freyCurve P.p P.hppos q P.hp_odd E heq hq hfixed
    exact ⟨φ, hφ⟩

/-- Full rational two-torsion survives on every actual Vélu target. -/
theorem IsVeluTarget.full_two_torsion (h : P.IsVeluTarget E) :
    ∃ f₂ : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective f₂ := by
  obtain ⟨φ, hφ⟩ := h.exists_rational_map
  obtain ⟨f₂, hf₂⟩ := P.frey_full_two_torsion
  exact fullTwoTorsion_survives_of_kernel_killed
    (Nat.coprime_two_left.mpr P.hp_odd) f₂ hf₂ φ hφ

end FreyPackage
