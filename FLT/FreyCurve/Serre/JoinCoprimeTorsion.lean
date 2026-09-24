/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Joining coprime torsion subgroups

The full two-torsion and an odd-order cyclic subgroup of an abelian group
combine into an embedded product. This is the elementary group-theoretic
leaf of the Serre bridge for the Frey curve.
-/

@[expose] public section

namespace SerrePlan

/-- Injective maps from full two-torsion and from `ZMod p` into an abelian
group combine into an injective map from their product when `2` and `p`
are coprime. The product map sends `(u, t)` to `f₂ u + fₚ t`. -/
theorem join_coprime_torsion {A : Type*} [AddCommGroup A] {p : ℕ}
    (hp : Nat.Coprime 2 p)
    (f₂ : (ZMod 2 × ZMod 2) →+ A) (h₂ : Function.Injective f₂)
    (fₚ : ZMod p →+ A) (hₚ : Function.Injective fₚ) :
    ∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ A, Function.Injective f := by
  refine ⟨f₂.coprod fₚ, (injective_iff_map_eq_zero (f₂.coprod fₚ)).mpr ?_⟩
  rintro ⟨u, t⟩ h
  change f₂ u + fₚ t = 0 at h
  have htwo : 2 • fₚ t = 0 := by
    have := congrArg (fun a : A ↦ 2 • a) h
    simpa only [nsmul_add, ← map_nsmul, ZModModule.char_nsmul_eq_zero,
      map_zero, zero_add, nsmul_zero] using this
  have hprime : p • fₚ t = 0 := by
    rw [← map_nsmul, ZModModule.char_nsmul_eq_zero, map_zero]
  have hord : addOrderOf (fₚ t) ∣ 1 := by
    simpa only [hp.gcd_eq_one] using Nat.dvd_gcd
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hprime)
  have ht : fₚ t = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hord)
  have hu : f₂ u = 0 := by simpa only [ht, add_zero] using h
  exact Prod.ext (h₂ (hu.trans (map_zero f₂).symm))
    (hₚ (ht.trans (map_zero fₚ).symm))

end SerrePlan
