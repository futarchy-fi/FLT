/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothRelativeCotangentRank
public import FLT.Mazur.BaseChangeCotangentFieldRank

/-!
# Relative dimension detected at arbitrary field points

A locally standard-smooth algebra has the prescribed differential rank at
any field-valued point. This detects the dimension of an original standard
chart from a single point of its cartesian fiber.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.SmoothFieldCotangentRank

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u

/-- Relative dimension computes the cotangent rank at every field-valued point. -/
theorem finrank_eq (R A B : Type u) [CommRing R] [CommRing A] [Field B]
    [Algebra R A] [Algebra A B] (d : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (algebraMap R A)) :
    Module.finrank B (B ⊗[A] Ω[A⁄R]) = d := by
  obtain ⟨s, hs, hstd⟩ := h
  let p := RingHom.ker (algebraMap A B)
  have hpprime : p.IsPrime := RingHom.ker_isPrime (algebraMap A B)
  have hex : ∃ f ∈ s, f ∉ p := by
    by_contra! he
    have hp : Ideal.span s ≤ p := Ideal.span_le.mpr he
    rw [hs] at hp
    exact hpprime.ne_top (top_le_iff.mp hp)
  obtain ⟨f, hf, hfp⟩ := hex
  have hd := hstd f hf
  rw [← IsScalarTower.algebraMap_eq R A (Localization.Away f),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hd
  let _ := hd
  let L := Localization.Away f
  let _ : Algebra.IsStandardSmooth R L :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := d)
  have hu : IsUnit (algebraMap A B f) := isUnit_iff_ne_zero.mpr hfp
  let g : L →+* B := IsLocalization.Away.lift f hu
  let _ := g.toAlgebra
  let _ : IsScalarTower A L B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (IsLocalization.Away.lift_eq (S := L) f hu a).symm)
  rw [LocalizedCotangentFieldRank.finrank_eq R A L B]
  exact (StandardSmoothFieldCotangentRank.relativeDimension_iff R L B d).mp inferInstance

/-- A relative smooth fiber detects the dimension of an original standard-smooth chart. -/
theorem relativeDimension_of_baseChange (R S A C B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing C] [Field B]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra S C] [Algebra A C]
    [IsScalarTower R S C] [IsScalarTower R A C] [Algebra.IsPushout R S A C]
    [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.IsStandardSmooth R A]
    (d : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (algebraMap S C)) :
    Algebra.IsStandardSmoothOfRelativeDimension d R A :=
  BaseChangeCotangentFieldRank.relativeDimension R S A C B d (finrank_eq S C B d h)

end FLT.Mazur.SmoothFieldCotangentRank
