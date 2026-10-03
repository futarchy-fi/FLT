/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CyclotomicQuadraticDetection
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # The actual modular cyclotomic determinant of a residual HR representation -/

@[expose] public section

namespace PadicInt

/-- A characteristic-p coefficient map factors through the canonical residue map. -/
theorem map_eq_cast_toZMod {p : ℕ} [Fact p.Prime]
    {k : Type*} [CommRing k] [CharP k p] (f : ℤ_[p] →+* k) (x : ℤ_[p]) :
    f x = ZMod.castHom (dvd_refl p) k (toZMod x) := by
  have hker : IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker f := by
    rw [maximalIdeal_eq_span_p, Ideal.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    change f (p : ℤ_[p]) = 0
    simp
  have h := hker (toZMod_spec (x := x))
  change f (x - (ZMod.cast (toZMod x) : ℤ_[p])) = 0 at h
  simpa only [map_sub, sub_eq_zero, ZMod.cast_eq_val, map_natCast,
    ZMod.castHom_apply] using h

end PadicInt

namespace GaloisRepresentation.IsHardlyRamified

/-- Reduction of the HR determinant agrees with D14's specified global character. -/
theorem det_eq_modularCyclotomic {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {k V : Type*} [Field k] [CharP k p] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [IsTopologicalRing k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified hpodd hV ρ) (g : Field.absoluteGaloisGroup ℚ) :
    (ρ g).det = ZMod.castHom (dvd_refl p) k (CyclotomicQuadratic.character p g) := by
  change ρ.det g = _
  rw [hρ.det, PadicInt.map_eq_cast_toZMod,
    cyclotomicCharacter.toZMod (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)]
  rfl

end GaloisRepresentation.IsHardlyRamified
