/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionCharts
public import FLT.Mazur.SectionDivisors
public import FLT.Mazur.SectionKernelLocal

/-!
# Smooth sections are relative effective Cartier divisors

Compatible affine charts identify the section ideal with the augmentation kernel.
Localizing its regular equation gives charts for the actual ideal sheaf of the section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

namespace SectionChart

variable {y : S} (C : SectionChart f s y)

/-- The compatible base chart is the full preimage of the source chart. -/
lemma preimage_source (hs : s ≫ f = 𝟙 S) : s ⁻¹ᵁ C.source.1 = C.base.1 := by
  apply le_antisymm
  · intro z hz
    have h := C.source_le hz
    have hz' : f (s z) = z := by
      simpa using congrArg (fun g : S ⟶ S ↦ g z) hs
    change f (s z) ∈ C.base.1 at h
    rwa [hz'] at h
  · exact C.base_le

/-- The augmentation kernel is the actual section ideal on the source chart. -/
lemma ideal_ker_eq [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    s.ker.ideal C.source = RingHom.ker C.augmentation := by
  let := isClosedImmersion_section f s hs
  rw [Scheme.Hom.ker_apply]
  have h := C.preimage_source hs
  have hi : IsIso (homOfLE C.base_le) := by
    have he : homOfLE C.base_le = eqToHom h.symm := Subsingleton.elim _ _
    rw [he]
    infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso
    (S.presheaf.map (homOfLE C.base_le).op)).1
  exact (RingHom.ker_comp_of_injective _ hinj).symm

/-- A localized augmentation equation gives a chart for the section ideal sheaf. -/
lemma cartierChart_basicOpen [IsSeparated f] (hs : s ≫ f = 𝟙 S)
    (h t : Γ(X, C.source))
    (heq : (RingHom.ker C.augmentation).map
      (algebraMap _ (Localization.Away h)) =
        Ideal.span {algebraMap _ (Localization.Away h) t})
    (ht : IsRegular (algebraMap _ (Localization.Away h) t)) :
    CartierChart s.ker (X.affineBasicOpen h) := by
  let := C.source.2.isLocalization_basicOpen h
  let e := IsLocalization.algEquiv (Submonoid.powers h)
    (Localization.Away h) Γ(X, X.basicOpen h)
  have he : e.toRingHom.comp (algebraMap _ (Localization.Away h)) =
      algebraMap Γ(X, C.source) Γ(X, X.basicOpen h) := e.toAlgHom.comp_algebraMap
  have hmap := congrArg (Ideal.map e.toRingHom) heq
  rw [Ideal.map_map, he, Ideal.map_span, Set.image_singleton] at hmap
  refine ⟨e (algebraMap _ (Localization.Away h) t), ?_, ?_⟩
  · rw [← isLeftRegular_iff_isRegular] at ht ⊢
    intro a b hab
    apply e.symm.injective
    exact ht (by simpa using congrArg e.symm hab)
  · rw [← s.ker.map_ideal_basicOpen C.source h, C.ideal_ker_eq hs]
    exact hmap

include C in
/-- Every compatible smooth section chart contains a Cartier neighborhood of its point. -/
lemma exists_cartierChart [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    ∃ U : X.affineOpens, s y ∈ U.1 ∧ CartierChart s.ker U := by
  let := C.algebra
  let := C.algebra_standardSmooth
  obtain ⟨g, hg⟩ := exists_etale_polynomial_coordinate
    (R := Γ(S, C.base)) (B := Γ(X, C.source))
  obtain ⟨h, hh, heq, ht⟩ := exists_etale_coordinate_kernel_eq g hg
    (C.augmentationAlgHom hs) C.sectionPrime.asIdeal C.ker_augmentation_le_sectionPrime
  refine ⟨X.affineBasicOpen h, ?_, C.cartierChart_basicOpen hs h _ heq ht⟩
  change s y ∈ X.basicOpen h
  have hx : C.source.2.fromSpec C.sectionPrime = s y :=
    C.source.2.fromSpec_primeIdealOf ⟨s y, C.mem_source⟩
  rw [← hx]
  change C.sectionPrime ∈ C.source.2.fromSpec ⁻¹ᵁ X.basicOpen h
  rwa [C.source.2.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]

end SectionChart

/-- A section of a smooth separated relative curve is relative effective Cartier. -/
theorem smoothSectionCartier (f : X ⟶ S) (s : S ⟶ X) : SmoothSectionCartier f s := by
  intro hf hsep hs
  apply (relativeEffectiveCartier_section_iff_charts f s hs).mpr
  intro y
  obtain ⟨C⟩ := exists_sectionChart f s hs y
  exact C.exists_cartierChart hs

end FLT.Mazur.FCurve
