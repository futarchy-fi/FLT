/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicPatchingArithmetic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The rings in the arithmetic patching square

We realize `ℤ[1/(dp)]` by first inverting `d` and then `p`. The maps to the local
rings and their scalar towers are explicit. In particular `d = 2, p = 3` gives
the coefficient rings of patching away from two.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A localization of a principal ideal ring is a principal ideal ring. -/
theorem localization_isPrincipalIdealRing (A B : Type*) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [Algebra A B] (T : Submonoid A) [IsLocalization T B] :
    IsPrincipalIdealRing B := by
  constructor
  intro I
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (I.under A)
  refine ⟨⟨algebraMap A B a, ?_⟩⟩
  rw [← IsLocalization.map_under T B I, ha, Ideal.map_span, Set.image_singleton]

namespace PadicPatching

/-- The global coefficient ring with `d` inverted. -/
abbrev Base (d : ℤ) := Localization.Away d

/-- The coefficient ring obtained by additionally inverting `p`. -/
abbrev Away (d : ℤ) (p : ℕ) := Localization.Away (p : Base d)

/-- Inverting one leaves the global ring of integers unchanged. -/
def baseOneEquivInt : Base 1 ≃ₐ[ℤ] ℤ :=
  (IsLocalization.atUnit ℤ (Base 1) (1 : ℤ) isUnit_one).symm

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [hd : Fact (¬ (p : ℤ) ∣ d)]

/-- The integer inverted in the global coefficient ring is a local unit. -/
theorem denominator_isUnit : IsUnit (d : ℤ_[p]) := by
  apply PadicInt.isUnit_iff.mpr
  exact le_antisymm (PadicInt.norm_le_one _)
    (le_of_not_gt (mt (PadicInt.norm_int_lt_one_iff_dvd d).mp Fact.out))

/-- The map from `ℤ[1/d]` into the local integers. -/
def baseToLocal : Base d →+* ℤ_[p] :=
  IsLocalization.Away.lift d (show IsUnit (algebraMap ℤ ℤ_[p] d) from denominator_isUnit p d)

instance : Algebra (Base d) ℤ_[p] := (baseToLocal p d).toAlgebra

instance : Algebra (Base d) ℚ_[p] := Algebra.compHom ℚ_[p] (baseToLocal p d)

instance : IsScalarTower (Base d) ℤ_[p] ℚ_[p] :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The map from the ring with `p` inverted into the local field. -/
def awayToField : Away d p →+* ℚ_[p] :=
  IsLocalization.Away.lift (p : Base d) (show IsUnit (algebraMap (Base d) ℚ_[p] p) by
    simpa using (isUnit_iff_ne_zero.mpr (show (p : ℚ_[p]) ≠ 0 by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)))

instance : Algebra (Away d p) ℚ_[p] := (awayToField p d).toAlgebra

instance : IsScalarTower (Base d) (Away d p) ℚ_[p] := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change _ = awayToField p d _
  unfold awayToField
  exact (IsLocalization.Away.lift_eq _ _ _).symm

instance : IsLocalization.Away (d * (p : ℤ)) (Away d p) := by
  have : IsLocalization.Away (algebraMap ℤ (Base d) (p : ℤ)) (Away d p) := by
    simpa using (inferInstance : IsLocalization.Away (p : Base d) (Away d p))
  exact IsLocalization.Away.mul' (Base d) (Away d p) d (p : ℤ)

/-- The iterated localization used for patching is the usual single localization. -/
def awayEquivSingle : Away d p ≃ₐ[ℤ] Localization.Away (d * (p : ℤ)) :=
  IsLocalization.algEquiv (Submonoid.powers (d * (p : ℤ))) _ _

instance : IsPrincipalIdealRing (Base d) :=
  localization_isPrincipalIdealRing ℤ (Base d) (Submonoid.powers d)

include hd in
omit [Fact p.Prime] in
/-- The denominator is nonzero because it is not divisible by `p`. -/
theorem denominator_ne_zero : d ≠ 0 := by
  intro h
  exact (Fact.out : ¬ (p : ℤ) ∣ d) (h ▸ dvd_zero _)

instance [NeZero d] : IsDomain (Base d) := Localization.Away.isDomain (NeZero.ne d)

instance : FaithfulSMul (Away d p) ℚ_[p] := by
  apply (faithfulSMul_iff_algebraMap_injective (Away d p) ℚ_[p]).mpr
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (d * (p : ℤ))) (Away d p) (algebraMap (Away d p) ℚ_[p])
  intro x hx
  have hx0 : x = 0 := by
    have : (x : ℚ_[p]) = 0 := by simpa using hx
    exact_mod_cast this
  simp [hx0]

instance [NeZero d] : IsDomain (Away d p) :=
  IsLocalization.Away.isDomain (R := ℤ) (x := d * (p : ℤ)) (Away d p)
    (mul_ne_zero (NeZero.ne d) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

instance : IsPrincipalIdealRing (Away d p) :=
  localization_isPrincipalIdealRing (Base d) (Away d p) (Submonoid.powers (p : Base d))

end PadicPatching
end ThreeAdicPlan
