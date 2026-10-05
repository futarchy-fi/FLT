/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.Contracts
public import FLT.Mazur.DedekindPointExtension

/-!
# Integral extension of rational points on the Mazur base

The localization Z[1/(2p)] is Dedekind for p ≠ 0 and Q is its fraction field
with the canonical map. Properness therefore extends every rational point
uniquely to a section, proving the G1Extension consumer contract. This does not
construct the proper modular curve or the assignment of its rational points.

Source: Mazur (1977), III §5, p. 159; the valuative criterion and gluing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

namespace FLT.Mazur

namespace IntegralBase

/-- The integral Mazur base is a Dedekind domain. -/
theorem baseRing_isDedekindDomain {p : ℕ} (hp : p ≠ 0) : IsDedekindDomain (BaseRing p) := by
  have hn : 2 * (p : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hp)
  let : IsDomain (BaseRing p) := Localization.Away.isDomain hn
  exact IsLocalization.isDedekindDomain ℤ
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hn)) (BaseRing p)

/-- Any rational spectrum map to the base is the canonical generic map. -/
theorem generic_unique {p : ℕ} (hp : p ≠ 0) (g : Spec (.of ℚ) ⟶ Base p) :
    g = generic hp := by
  rw [← Spec.map_preimage g]
  unfold generic
  congr 1
  apply CommRingCat.hom_ext
  exact genericMap_unique hp _

set_option backward.isDefEq.respectTransparency false in
/-- Every rational point of a proper scheme over Z[1/(2p)] extends uniquely. -/
theorem existsUnique_section {p : ℕ} (hp : p ≠ 0) (X : Over (Base p)) [IsProper X.hom]
    (x : Points X (generic hp)) :
    ∃! y : Sections X, Sections.restrict (generic hp) y = x := by
  let : IsDedekindDomain (BaseRing p) := baseRing_isDedekindDomain hp
  let : Algebra (BaseRing p) ℚ := (genericMap hp).toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := BaseRing p) (A := ℚ)
    fun n => (genericMap_algebraMap hp n).symm
  let : IsFractionRing (BaseRing p) ℚ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers (2 * (p : ℤ))) (BaseRing p) ℚ
  exact Sections.existsUnique_of_dedekind (CommRingCat.of (BaseRing p)) ℚ X x

end IntegralBase

/-- The integral extension contract for the supplied rational moduli points. -/
def G1Extension {p : ℕ} (D : IntegralData p) : Prop :=
  ∀ t : PrimePoint p, ∃! x : Sections D.X, genericSection D x = D.primePoint t

/-- Properness proves G1Extension for every supplied assignment of rational points. -/
theorem g1Extension_of_isProper {p : ℕ} (hp : p ≠ 0) (D : IntegralData p)
    [IsProper D.X.hom] : G1Extension D := by
  intro t
  have hg := IntegralBase.generic_unique hp D.generic
  have h := IntegralBase.existsUnique_section hp D.X
  rw [← hg] at h
  exact h (D.primePoint t)

end FLT.Mazur
