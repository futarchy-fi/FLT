/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierBaseChange
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Section images and regular coordinates

A section of a separated morphism is a closed immersion. Its scheme-theoretic image
is isomorphic to the base, so the flatness part of the relative Cartier condition
is automatic. The Cartier condition only needs to be checked along the image.

For a standard smooth algebra of relative dimension one, an augmentation supplies
a regular element in its kernel using an étale coordinate. This does not yet show
that the element generates the kernel on a neighborhood. That local generation
step and its passage to scheme charts remain necessary for `SmoothSectionCartier`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

section Geometry

variable {X S T : Scheme.{u}}

/-- A section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_section (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  exact IsClosedImmersion.of_comp s f

/-- The closed subscheme defined by the section kernel is its source. -/
def sectionImageIso (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) : s.ker.subscheme ≅ S := by
  let := isClosedImmersion_section f s hs
  exact (asIso s.toImage).symm

/-- The image comparison respects the embedding into the ambient scheme. -/
@[reassoc (attr := simp)]
lemma sectionImageIso_hom_section (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) :
    (sectionImageIso f s hs).hom ≫ s = s.ker.subschemeι := by
  let := isClosedImmersion_section f s hs
  change inv s.toImage ≫ s = s.imageι
  exact (IsIso.inv_comp_eq _).mpr s.toImage_imageι.symm

/-- The image comparison is precisely the structure morphism to the base. -/
lemma sectionImageIso_hom (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) :
    (sectionImageIso f s hs).hom = s.ker.subschemeι ≫ f := by
  rw [← sectionImageIso_hom_section f s hs, Category.assoc, hs, Category.comp_id]

/-- In particular the section image is isomorphic over the base to its identity family. -/
def sectionImageOverIso (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) : Over.mk (s.ker.subschemeι ≫ f) ≅ Over.mk (𝟙 S) :=
  Over.isoMk (sectionImageIso f s hs) (by simp [sectionImageIso_hom])

/-- Flatness of a section divisor does not require smoothness or a local equation. -/
theorem flat_sectionImage (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) : Flat (s.ker.subschemeι ≫ f) := by
  rw [← sectionImageIso_hom f s hs]
  infer_instance

/-- For a section, the relative Cartier condition reduces to the absolute one. -/
theorem relativeEffectiveCartier_section_iff (f : X ⟶ S) (s : S ⟶ X)
    [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    RelativeEffectiveCartier f s.ker ↔ EffectiveCartier s.ker :=
  ⟨And.left, fun h ↦ ⟨h, flat_sectionImage f s hs⟩⟩

/-- The support of a section kernel is its actual image, with no extra closure points. -/
lemma support_section_ker (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) : (s.ker.support : Set X) = Set.range s := by
  let := isClosedImmersion_section f s hs
  rw [s.support_ker, s.isClosedEmbedding.isClosed_range.closure_eq]

/-- Away from the support an ideal restricts to the unit ideal. -/
lemma comap_eq_top_of_disjoint_support (I : X.IdealSheafData) (W : X.Opens)
    (hW : ∀ x ∈ W, x ∉ I.support) : I.comap W.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [I.support_comap]
  ext x
  exact iff_false_intro (hW x.1 x.2)

/-- Outside its support every ideal has a Cartier chart with a unit equation. -/
lemma exists_cartierChart_of_notMem_support (I : X.IdealSheafData) {x : X}
    (hx : x ∉ I.support) : ∃ U : X.affineOpens, x ∈ U.1 ∧ CartierChart I U := by
  let W : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hI : EffectiveCartier (I.comap W.ι) := by
    rw [comap_eq_top_of_disjoint_support I W (fun _ h ↦ h)]
    exact effectiveCartier_top
  exact (effectiveCartier_restrict_iff I W).mp hI x hx

/-- Local generation only needs to be proved at points of the closed subscheme. -/
theorem effectiveCartier_iff_on_support (I : X.IdealSheafData) :
    EffectiveCartier I ↔ ∀ x ∈ I.support,
      ∃ U : X.affineOpens, x ∈ U.1 ∧ CartierChart I U := by
  classical
  refine ⟨fun h x _ ↦ h x, fun h x ↦ ?_⟩
  by_cases hx : x ∈ I.support
  · exact h x hx
  · exact exists_cartierChart_of_notMem_support I hx

/-- A section divisor is relative Cartier exactly when its image points have charts. -/
theorem relativeEffectiveCartier_section_iff_charts (f : X ⟶ S) (s : S ⟶ X)
    [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    RelativeEffectiveCartier f s.ker ↔ ∀ y : S,
      ∃ U : X.affineOpens, s y ∈ U.1 ∧ CartierChart s.ker U := by
  rw [relativeEffectiveCartier_section_iff f s hs, effectiveCartier_iff_on_support]
  simp only [← SetLike.mem_coe, support_section_ker f s hs, Set.forall_mem_range]

/-- The flatness conclusion for section images survives arbitrary base change. -/
theorem flat_sectionImage_baseChange (f : X ⟶ S) (s : S ⟶ X) [IsSeparated f]
    (hs : s ≫ f = 𝟙 S) (g : T ⟶ S) :
    Flat ((s.ker.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  let := flat_sectionImage f s hs
  exact flat_divisor_baseChange f g s.ker

end Geometry

section Algebra

open Polynomial

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A polynomial graph has a regular equation over any commutative base ring. -/
theorem regular_polynomial_section_equation (a : R) :
    IsRegular (X - C a : R[X]) ∧
      RingHom.ker (evalRingHom a) = Ideal.span {X - C a} :=
  ⟨(monic_X_sub_C a).isRegular, ker_evalRingHom a⟩

/-- The quotient of a polynomial graph is flat over the base, including nonreduced bases. -/
theorem flat_polynomial_section_quotient (a : R) :
    Module.Flat R (R[X] ⧸ Ideal.span {X - C a}) :=
  Module.Flat.of_linearEquiv (quotientSpanXSubCAlgEquiv a).toLinearEquiv

/-- Standard smooth dimension one gives an étale univariate coordinate. -/
theorem exists_etale_polynomial_coordinate
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B] :
    ∃ g : R[X] →ₐ[R] B, g.toRingHom.Etale := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 R B
  let e := (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm
  refine ⟨g.comp e.toAlgHom, ?_⟩
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective e.bijective) hg

/-- Pulling the translated coordinate through a flat map proves its regularity. -/
lemma isRegular_coordinate_of_flat (g : R[X] →ₐ[R] B) (hg : g.toRingHom.Flat)
    (a : R) : IsRegular (g (X - C a)) := by
  let := g.toRingHom.toAlgebra
  let : Module.Flat R[X] B := hg
  rw [← isLeftRegular_iff_isRegular]
  convert! (Module.Flat.isSMulRegular_of_isRegular (M := B)
    (monic_X_sub_C a).isRegular)

/-- An augmented smooth relative curve algebra has a regular element in its kernel.
Equality of the localized kernel with the principal ideal is a further step. -/
theorem exists_regular_mem_ker_of_standardSmooth
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B] (ε : B →ₐ[R] R) :
    ∃ t : B, IsRegular t ∧ t ∈ RingHom.ker ε.toRingHom := by
  obtain ⟨g, hg⟩ := exists_etale_polynomial_coordinate (R := R) (B := B)
  let a := ε (g X)
  refine ⟨g (X - C a), isRegular_coordinate_of_flat g
    ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp hg).2.flat a, ?_⟩
  change ε (g (X - C a)) = 0
  have hgC (r : R) : g (C r) = algebraMap R B r := g.commutes r
  rw [map_sub, map_sub, hgC, ε.commutes]
  exact sub_self _

end Algebra

end FLT.Mazur.FCurve
