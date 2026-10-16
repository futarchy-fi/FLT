/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatSectionLiftIdeal
public import FLT.Mazur.SectionLiftCertificateSourceChange
public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Faithfully flat descent with new lifting multipliers

Both the boundary ring and its tested source may be extended. Flatness
identifies the resulting source ideal with extension of the original ideal.
Faithful flatness then constructs an original finite source certificate,
even when every multiplier and every coefficient in the given certificate
lives only after scalar extension.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatSectionLiftCertificate
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] (g : B →ₐ[A] C)
  (S : Type*) [CommRing S] [Algebra A S] [Module.Flat A S]

local notation "f" => algebraMap A B
local notation "fs" => algebraMap S (S ⊗[A] B)
set_option quotPrecheck false in
local notation "gs" => (FlatAlgebraEqualizer.tensorMap S g).toRingHom
set_option quotPrecheck false in
local notation "j" => (Algebra.TensorProduct.includeRight : C →ₐ[A] S ⊗[A] C).toRingHom

/-- The tested ideal after flat extension is exactly the extended original tested ideal. -/
theorem sourceIdeal_map (t : B) :
    sectionLiftSourceIdeal fs gs (1 ⊗ₜ[A] t) =
      (sectionLiftSourceIdeal f g.toRingHom t).map j := by
  unfold sectionLiftSourceIdeal
  rw [← FlatSectionLiftIdeal.ideal_map, Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  change (FlatAlgebraEqualizer.tensorMap S g)
    (algebraMap A S a ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ[A] g (algebraMap A B a)
  change algebraMap A S a ⊗ₜ[A] g 1 = 1 ⊗ₜ[A] g (algebraMap A B a)
  rw [map_one, g.commutes, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
  simp only [Algebra.smul_def, mul_one]

variable [Module.FaithfullyFlat A S]
omit [Module.Flat A S] in
section

/-- Testing the extended section detects certification on the unchanged original source. -/
theorem certified_iff (t : B) :
    (1 ⊗ₜ[A] t) ∈ sourceCertifiedSections fs gs ↔
      t ∈ sourceCertifiedSections f g.toRingHom := by
  let _ : Algebra C (S ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let _ : Module.FaithfullyFlat C (S ⊗[A] C) :=
    Module.FaithfullyFlat.of_linearEquiv C (C ⊗[A] S)
      (Algebra.TensorProduct.commRight A C S).symm.toLinearEquiv
  change sectionLiftSourceIdeal fs gs (1 ⊗ₜ[A] t) = ⊤ ↔ _
  rw [sourceIdeal_map]
  change (sectionLiftSourceIdeal f g.toRingHom t).map (algebraMap C (S ⊗[A] C)) = ⊤ ↔
    sectionLiftSourceIdeal f g.toRingHom t = ⊤
  constructor
  · intro h
    apply Ideal.map_injective_of_faithfullyFlat (B := S ⊗[A] C)
    exact h.trans (Ideal.map_top _).symm
  · intro h
    rw [h, Ideal.map_top]

/-- A certificate with genuinely new denominators yields an original finite coefficient identity. -/
theorem certificate_descends (t : B)
    (h : ∃ c : sectionLiftIdeal fs (1 ⊗ₜ[A] t) →₀ S ⊗[A] C,
      c.sum (fun a b ↦ b * gs (fs a.val)) = 1) :
    ∃ c : sectionLiftIdeal f t →₀ C,
      c.sum (fun a b ↦ b * g (f a.val)) = 1 := by
  exact (mem_sourceCertifiedSections_iff f g.toRingHom t).mp
    ((certified_iff g S t).mp ((mem_sourceCertifiedSections_iff fs gs _).mpr h))

end

end FLT.Mazur.FlatSectionLiftCertificate
