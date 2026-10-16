/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundFlatSectionLiftIdeal
public import FLT.Mazur.FaithfullyFlatSectionLift

/-!
# Boundary certificate descent along the coefficient ground

Faithfully flat extension of the original coefficient ground detects the
original finite source certificate. No algebra over an invariant quotient
or finite generation of its invariant ring is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GroundFlatSectionLiftCertificate
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A →ₐ[R] B) (g : B →ₐ[R] C)
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
set_option quotPrecheck false in
local notation "fs" => (FlatAlgebraEqualizer.tensorMap S f).toRingHom
set_option quotPrecheck false in
local notation "gs" => (FlatAlgebraEqualizer.tensorMap S g).toRingHom
set_option quotPrecheck false in
local notation "j" => (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toRingHom

/-- Both source testing and restriction commute with extension of the ground ring. -/
theorem sourceIdeal_map (t : B) :
    sectionLiftSourceIdeal fs gs (1 ⊗ₜ[R] t) =
      (sectionLiftSourceIdeal f.toRingHom g.toRingHom t).map j := by
  unfold sectionLiftSourceIdeal
  rw [← GroundFlatSectionLiftIdeal.ideal_map, Ideal.map_map, Ideal.map_map]
  congr 1

variable [Module.FaithfullyFlat R S]
omit [Module.Flat R S] in
section

/-- A certificate with arbitrary new ground coefficients descends to the original source. -/
theorem certified_iff (t : B) :
    (1 ⊗ₜ[R] t) ∈ sourceCertifiedSections fs gs ↔
      t ∈ sourceCertifiedSections f.toRingHom g.toRingHom := by
  let _ : Algebra C (S ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  let _ : Module.FaithfullyFlat C (S ⊗[R] C) :=
    Module.FaithfullyFlat.of_linearEquiv C (C ⊗[R] S)
      (Algebra.TensorProduct.commRight R C S).symm.toLinearEquiv
  change sectionLiftSourceIdeal fs gs (1 ⊗ₜ[R] t) = ⊤ ↔ _
  rw [sourceIdeal_map]
  change (sectionLiftSourceIdeal f.toRingHom g.toRingHom t).map
    (algebraMap C (S ⊗[R] C)) = ⊤ ↔
      sectionLiftSourceIdeal f.toRingHom g.toRingHom t = ⊤
  constructor
  · intro h
    apply Ideal.map_injective_of_faithfullyFlat (B := S ⊗[R] C)
    exact h.trans (Ideal.map_top _).symm
  · intro h
    rw [h, Ideal.map_top]

/-- The output is a finite identity with unchanged original multipliers and coefficients. -/
theorem certificate_descends (t : B)
    (h : ∃ c : sectionLiftIdeal fs (1 ⊗ₜ[R] t) →₀ S ⊗[R] C,
      c.sum (fun a b ↦ b * gs (fs a.val)) = 1) :
    ∃ c : sectionLiftIdeal f.toRingHom t →₀ C,
      c.sum (fun a b ↦ b * g (f a.val)) = 1 :=
  (mem_sourceCertifiedSections_iff f.toRingHom g.toRingHom t).mp
    ((certified_iff f g S t).mp ((mem_sourceCertifiedSections_iff fs gs _).mpr h))

/-- A lift after faithfully flat ground change is a genuine original lift. -/
theorem lift_descends (t : B) (a : S ⊗[R] A)
    (ha : fs a = 1 ⊗ₜ[R] t) : ∃ b : A, f b = t := by
  apply (FaithfullyFlatSectionLift.exists_lift_iff f.toLinearMap S t).mp
  exact ⟨a, (FlatAlgebraEqualizer.tensorMap_eq_lTensor S f a).symm.trans ha⟩

end
end FLT.Mazur.GroundFlatSectionLiftCertificate
