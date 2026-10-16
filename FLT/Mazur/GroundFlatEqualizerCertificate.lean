/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatAlgebraEqualizerNaturality
public import FLT.Mazur.GroundFlatSectionLiftCertificate
public import FLT.Mazur.SectionLiftCertificateEquiv

/-!
# Descent of certificates from full ground-extended relation equations

The tested restriction is the map between the full new equalizers, not merely
a tensor map between abstract invariant rings. Naturality identifies the two
and faithfully flat ground descent returns the original finite coefficient
identity. Both original endpoint equations remain present throughout.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GroundFlatEqualizerCertificate
open FlatAlgebraEqualizer
variable {R A C A' C' : Type*}
  [CommRing R] [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
  [Algebra R A] [Algebra R C] [Algebra R A'] [Algebra R C']
  (p q : A →ₐ[R] C) (p' q' : A' →ₐ[R] C')
  (u : A →ₐ[R] A') (v : C →ₐ[R] C')
  (hp : p'.comp u = v.comp p) (hq : q'.comp u = v.comp q)
  (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
local notation "f" => equalizerMap p q p' q' u v hp hq
set_option quotPrecheck false in
local notation "g" => (AlgHom.equalizer p' q').val
local notation "fs" => tensorEqualizerMap p q p' q' u v hp hq S
set_option quotPrecheck false in
local notation "gs" => (AlgHom.equalizer (tensorMap S p') (tensorMap S q')).val

/-- Full new relation invariants certify exactly the original boundary coefficient. -/
theorem certified_iff (t : AlgHom.equalizer p' q') :
    comparison p' q' S (1 ⊗ₜ[R] t) ∈ sourceCertifiedSections (fs).toRingHom (gs).toRingHom ↔
      t ∈ sourceCertifiedSections (f).toRingHom (g).toRingHom := by
  have h := SectionLiftCertificateEquiv.certified_iff
    (tensorMap S f).toRingHom (tensorMap S g).toRingHom (fs).toRingHom (gs).toRingHom
    (comparison p q S).toRingEquiv (comparison p' q' S).toRingEquiv (RingEquiv.refl _)
    (comparison_natural p q p' q' u v hp hq S) (fun _ ↦ rfl) (1 ⊗ₜ[R] t)
  exact h.trans (GroundFlatSectionLiftCertificate.certified_iff f g S t)

/-- A finite identity in full new relation coordinates constructs one on the original source. -/
theorem certificate_descends (t : AlgHom.equalizer p' q')
    (h : comparison p' q' S (1 ⊗ₜ[R] t) ∈
      sourceCertifiedSections (fs).toRingHom (gs).toRingHom) :
    ∃ c : sectionLiftIdeal (f).toRingHom t →₀ A',
      c.sum (fun a b ↦ b * (f a.val).val) = 1 :=
  (mem_sourceCertifiedSections_iff (f).toRingHom (g).toRingHom t).mp
    ((certified_iff p q p' q' u v hp hq S t).mp h)

/-- Actual lifts in full new invariant coordinates descend to actual original invariant lifts. -/
theorem lift_descends (t : AlgHom.equalizer p' q')
    (a : AlgHom.equalizer (tensorMap S p) (tensorMap S q))
    (ha : fs a = comparison p' q' S (1 ⊗ₜ[R] t)) :
    ∃ b : AlgHom.equalizer p q, f b = t := by
  apply GroundFlatSectionLiftCertificate.lift_descends f S t ((comparison p q S).symm a)
  apply (comparison p' q' S).injective
  change comparison p' q' S (tensorMap S f _) = _
  rw [← comparison_natural, AlgEquiv.apply_symm_apply]
  exact ha

end FLT.Mazur.GroundFlatEqualizerCertificate
