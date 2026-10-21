/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarComparisonLocalGeometry
public import FLT.Mazur.SchemeScalarImageNeighborhoodCoverage
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Effective descent for the full original relation on an image neighborhood

Local image geometry and full comparison coverage identify the actual
restricted relation with the full restricted kernel pair. The image open
then represents its compatible functions, including all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarComparisonNeighborhoodDescent
open SchemeScalarImageQuotient SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {D X : Scheme.{0}}
  (f : X ⟶ Spec (.of R)) (a b : D ⟶ X) (h : a ≫ f = b ≫ f)
  (U : (Spec (.of (Scalars f))).Opens)
set_option quotPrecheck false
local notation "c" => projection f
local notation "u" => pullback.fst f f
local notation "k" => pullback.lift a b h
local notation "W" => u ⁻¹ᵁ (c ⁻¹ᵁ U)
local notation "kU" => k ∣_ W

/-- The first endpoint of the full relation restricted over the original image open. -/
def first : (k ⁻¹ᵁ W).toScheme ⟶ (c ⁻¹ᵁ U).toScheme := kU ≫ (u ∣_ (c ⁻¹ᵁ U))

/-- The second endpoint of the same full relation, with its independent coordinate. -/
def second : (k ⁻¹ᵁ W).toScheme ⟶ (c ⁻¹ᵁ U).toScheme :=
  kU ≫ SchemeScalarImageKernelNeighborhood.second f U

/-- Restriction retains the original first endpoint. -/
@[reassoc] theorem first_ι : first f a b h U ≫ (c ⁻¹ᵁ U).ι = (k ⁻¹ᵁ W).ι ≫ a := by
  simp only [first, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    pullback.lift_fst]

/-- Restriction retains the original second endpoint. -/
@[reassoc] theorem second_ι : second f a b h U ≫ (c ⁻¹ᵁ U).ι = (k ⁻¹ᵁ W).ι ≫ b := by
  simp only [second, Category.assoc, SchemeScalarImageKernelNeighborhood.second_ι,
    morphismRestrict_ι_assoc, pullback.lift_snd]

variable [Etale a] [Etale ((projection f) ∣_ U)] [Mono (pullback.lift a b h)]
  [Surjective ((pullback.lift a b h) ∣_
    ((pullback.fst f f) ⁻¹ᵁ ((projection f) ⁻¹ᵁ U)))]

/-- Local etale geometry and coverage identify the full comparison scheme, not only its points. -/
theorem comparison_isIso : IsIso kU := by
  let _ : IsOpenImmersion kU :=
    SchemeScalarComparisonLocalGeometry.comparison_isOpenImmersion f a b h U
  exact (isIso_iff_isOpenImmersion_and_surjective kU).mpr ⟨inferInstance, inferInstance⟩

/-- The actual restricted relation is the whole kernel pair over the original image open. -/
theorem relation_isPullback :
    IsPullback (first f a b h U) (second f a b h U) (c ∣_ U) (c ∣_ U) := by
  let _ := comparison_isIso f a b h U
  apply (SchemeScalarImageKernelNeighborhood.kernel_isPullback f U).of_iso
    (asIso kU).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, first, Iso.symm_hom, asIso_inv,
      IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, second, Iso.symm_hom, asIso_inv,
      IsIso.inv_hom_id_assoc]
  · simp
  · simp

variable [IsAffine X] [IsIntegralHom ((projection f) ∣_ U)]

/-- Full relation compatibility descends uniquely to the original image neighborhood. -/
theorem sections_existsUnique (t : Γ((c ⁻¹ᵁ U).toScheme, ⊤))
    (ht : (first f a b h U).appTop t = (second f a b h U).appTop t) :
    ∃! s : Γ(U.toScheme, ⊤), (c ∣_ U).appTop s = t := by
  let _ := projection_restrict_effectiveEpi_of_flat_integral f U
  exact SchemeEffectiveEpiSections.sections_existsUnique (relation_isPullback f a b h U) t ht

/-- The original image neighborhood ring is the full relation's compatible-function ring. -/
def sectionsRingEquiv :
    Γ(U.toScheme, ⊤) ≃+* compatibleFunctions (first f a b h U) (second f a b h U) := by
  let _ := projection_restrict_effectiveEpi_of_flat_integral f U
  exact SchemeEffectiveEpiSections.sectionsRingEquiv (relation_isPullback f a b h U)

end FLT.Mazur.SchemeScalarComparisonNeighborhoodDescent
