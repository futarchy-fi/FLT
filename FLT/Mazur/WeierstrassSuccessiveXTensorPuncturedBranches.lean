/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Branches forced by the full punctured tensor equation

At a closed-fiber point the incidence relation kills the boundary coordinate.
The slope equation then gives the two branches without coefficient-depth bounds.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]
local notation "T" => ScalarExtension W s π b3 b4 b6 S
local notation "t" => tensorCoord W s π b3 b4 b6 S 0
local notation "v" => tensorCoord W s π b3 b4 b6 S 1
local notation "u" => tensorCoord W s π b3 b4 b6 S 2
local notation "α" => algebraMap R T W.a₁
variable (p : PrimeSpectrum (ScalarExtension W s π b3 b4 b6 S))
  (hp : algebraMap R (ScalarExtension W s π b3 b4 b6 S) π ∈ p.asIdeal)
  (hu : tensorCoord W s π b3 b4 b6 S 2 ∉ p.asIdeal)

include hp hu in
/-- Nonzero horizontal coordinate forces the incidence coordinate to vanish. -/
theorem tensorPunctured_incidence_mem : t ∈ p.asIdeal := by
  have h : t * u ∈ p.asIdeal := by
    rw [baseChange_incidence, ← IsScalarTower.algebraMap_apply R S]
    exact hp
  exact (p.isPrime.mem_or_mem h).resolve_right hu

include hp hu in
/-- The full tensor equation forces one of the two original slope branches. -/
theorem tensorPunctured_slope_cases (hs : algebraMap R T s ∈ p.asIdeal)
    (h2 : algebraMap R T W.a₂ ∈ p.asIdeal) :
    v ∈ p.asIdeal ∨ v + α ∈ p.asIdeal := by
  have ht := tensorPunctured_incidence_mem W s π b3 b4 b6 S p hp hu
  let q := Ideal.Quotient.mk p.asIdeal
  have zero (a : T) (ha : a ∈ p.asIdeal) : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have he := congrArg q (baseChange_equation W s π b3 b4 b6 S)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S, map_add, map_mul, map_pow,
    zero _ ht, zero _ hs, zero _ h2, mul_zero, zero_mul, add_zero,
    zero_pow (by decide : 2 ≠ 0)] at he
  have hz : q (v * (v + α)) = 0 := by
    simp only [map_mul, map_add]
    linear_combination he
  exact p.isPrime.mem_or_mem (Ideal.Quotient.eq_zero_iff_mem.mp hz)

include hp hu in
/-- The contracted ordinate and its opposite-branch factor exhaust every punctured input. -/
theorem tensorPunctured_contracted_cases (hs : algebraMap R T s ∈ p.asIdeal)
    (h2 : algebraMap R T W.a₂ ∈ p.asIdeal) :
    u * v ∈ p.asIdeal ∨ u * v + α * u ∈ p.asIdeal := by
  rcases tensorPunctured_slope_cases W s π b3 b4 b6 S p hp hu hs h2 with h | h
  · exact Or.inl (p.asIdeal.mul_mem_left _ h)
  · apply Or.inr
    convert p.asIdeal.mul_mem_left u h using 1
    ring

include hu in
/-- A unit linear coefficient separates the two contracted branches on the puncture. -/
theorem tensorPunctured_contracted_not_both (h1 : IsUnit W.a₁) :
    ¬ (u * v ∈ p.asIdeal ∧ u * v + α * u ∈ p.asIdeal) := by
  rintro ⟨h, h'⟩
  have ha : α * u ∈ p.asIdeal := by
    simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem h' h
  rcases p.isPrime.mem_or_mem ha with ha | ha
  · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha (h1.map (algebraMap R T)))
  · exact hu ha

end FLT.Mazur.WeierstrassSuccessiveX
