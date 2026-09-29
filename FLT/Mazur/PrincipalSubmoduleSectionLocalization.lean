/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalSubmoduleCoordinates

/-!
# Localization of actual source sections

Restriction between the images of the principal charts for `f` and `f * g`
is localization at powers of `g`. All comparisons are constructed from restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum
open Scheme.Modules
open FLT.Mazur.PrincipalSubmoduleCoordinates

universe u

namespace FLT.Mazur.PrincipalSubmoduleSectionLocalization

variable {R : CommRingCat.{u}} (U : (Spec R).Opens) (f g : R) (hf : basicOpen f ≤ U)

/-- The basic open in the first chart has precisely the product chart's image. -/
lemma chart_basicOpen_image :
    chart U f hf ''ᵁ basicOpen (algebraMap R (Localization.Away f) g) =
      chart U (f * g) ((basicOpen_mul_le_left f g).trans hf) ''ᵁ ⊤ := by
  have h : principalMap f ''ᵁ basicOpen (algebraMap R (Localization.Away f) g) =
      basicOpen (f * g) := by
    have he := SpecMap_preimage_basicOpen
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) g
    have hi := congrArg (fun V : (Spec (CommRingCat.of (Localization.Away f))).Opens ↦
      principalMap f ''ᵁ V) he
    change principalMap f ''ᵁ _ = _ at hi
    refine hi.symm.trans ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [principalMap, basicOpen_mul]
  apply le_antisymm <;> rw [← Scheme.Hom.image_le_image_iff U.ι]
  all_goals simp only [← Scheme.Hom.comp_image, chart_comp, h]
  all_goals simp [principalMap]

variable {U} (L : U.toScheme.Modules)

/-- Sections on the image of the first chart. -/
abbrev sourceSections := Γ(L, chart U f hf ''ᵁ ⊤)

/-- Sections on the image of the product chart. -/
abbrev overlapSections :=
  Γ(L, chart U (f * g) ((basicOpen_mul_le_left f g).trans hf) ''ᵁ ⊤)

/-- The constructed comparison from chart sections to actual overlap sections. -/
def overlapIso :
    Γ(L.restrict (chart U f hf), basicOpen (algebraMap R (Localization.Away f) g)) ≅
      overlapSections f g hf L :=
  L.restrictAppIso (chart U f hf) _ ≪≫
    L.presheaf.mapIso (eqToIso (chart_basicOpen_image U f g hf).symm).op

/-- Affine chart sections carry the affine coordinate ring action. -/
local instance chartModule (N : (Spec (CommRingCat.of (Localization.Away f))).Modules)
    (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) :
    Module (Localization.Away f) Γ(N, V) :=
  inferInstanceAs (Module (Localization.Away f)
    (((modulesSpecToSheaf (R := CommRingCat.of (Localization.Away f))).obj N).obj.obj (op V)))

/-- Scalars on the first image are pulled back from its affine chart. -/
instance sourceModule : Module (Localization.Away f) (sourceSections f hf L) :=
  inferInstanceAs (Module (Localization.Away f) Γ(L.restrict (chart U f hf), ⊤))

/-- Scalars on the overlap use the same first chart and the proved image equality. -/
instance overlapModule : Module (Localization.Away f) (overlapSections f g hf L) :=
  (overlapIso f g hf L).symm.addCommGroupIsoToAddEquiv.module (Localization.Away f)

instance sourceBaseModule : Module R (sourceSections f hf L) :=
  Module.compHom _ (algebraMap R (Localization.Away f))

instance overlapBaseModule : Module R (overlapSections f g hf L) :=
  Module.compHom _ (algebraMap R (Localization.Away f))

instance sourceScalarTower :
    IsScalarTower R (Localization.Away f) (sourceSections f hf L) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

instance overlapScalarTower :
    IsScalarTower R (Localization.Away f) (overlapSections f g hf L) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The affine scalar, viewed as a function on an actual chart image. -/
def chartScalar (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) :
    Localization.Away f →+* Γ(U.toScheme, chart U f hf ''ᵁ V) :=
  (chart U f hf |>.appIso V).inv.hom.comp
    (((Spec (CommRingCat.of (Localization.Away f))).presheaf.map V.leTop.op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).inv.hom)

/-- The same scalar on the product image, transported along the proved equality. -/
def overlapScalar : Localization.Away f →+*
    Γ(U.toScheme, chart U (f * g) ((basicOpen_mul_le_left f g).trans hf) ''ᵁ ⊤) :=
  (U.toScheme.presheaf.map (eqToHom (chart_basicOpen_image U f g hf).symm).op).hom.comp
    (chartScalar f hf (basicOpen (algebraMap R (Localization.Away f) g)))

/-- The source action factors through the affine chart and its section scalars. -/
lemma source_smul (r : R) (x : sourceSections f hf L) :
    r • x = chartScalar f hf ⊤ (algebraMap R (Localization.Away f) r) • x := rfl

/-- The overlap action factors through the same affine chart and section scalars. -/
lemma overlap_smul (r : R) (x : overlapSections f g hf L) :
    r • x = overlapScalar f g hf (algebraMap R (Localization.Away f) r) • x := by
  change L.presheaf.map _
    (chartScalar f hf (basicOpen (algebraMap R (Localization.Away f) g))
      (algebraMap R (Localization.Away f) r) •
      ((L.restrictAppIso (chart U f hf) _).hom ((overlapIso f g hf L).inv x))) = _
  refine (L.map_smul (eqToHom (chart_basicOpen_image U f g hf).symm) _ _).trans ?_
  change _ • ((overlapIso f g hf L).hom ((overlapIso f g hf L).inv x)) = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- The overlap comparison is linear for the chart's scalar action. -/
def overlapLinear :
    Γ(L.restrict (chart U f hf), basicOpen (algebraMap R (Localization.Away f) g)) ≃ₗ[
      Localization.Away f] overlapSections f g hf L :=
  ((overlapIso f g hf L).symm.addCommGroupIsoToAddEquiv.linearEquiv
    (Localization.Away f)).symm

/-- The transported principal restriction, on actual sections of the two images. -/
def restriction : sourceSections f hf L →ₗ[Localization.Away f] overlapSections f g hf L :=
  (overlapLinear f g hf L).toLinearMap.comp
    (toSections (L.restrict (chart U f hf)) (algebraMap R (Localization.Away f) g))

/-- Transport gives exactly the restriction used in the inclusion-coordinate square. -/
lemma restriction_apply (x : sourceSections f hf L) :
    restriction f g hf L x =
      L.presheaf.map (homOfLE (chart_product_le U f g hf)).op x := by
  change L.presheaf.map _ ((L.restrictAppIso (chart U f hf) _).hom
    ((L.restrict (chart U f hf)).presheaf.map _ x)) = _
  rw [map_restrictAppIso_hom_apply]
  simp only [← L.presheaf.map_comp_apply]
  rfl

/-- The transported restriction commutes with the existing inclusion-coordinate square. -/
lemma restriction_coordinates {M : (Spec R).Modules} [M.IsQuasicoherent]
    (i : L ⟶ M.restrict U.ι) (x : sourceSections f hf L) :
    coordinates M (f * g)
        (inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf)
          (restriction f g hf L x)) =
      TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g
        (coordinates M f (inclusionSection i f hf x)) := by
  rw [restriction_apply]
  exact inclusionSection_coordinates_restriction i f g hf x

variable [L.IsQuasicoherent]

/-- Localization on the affine chart transports to the actual section restriction. -/
instance restriction_isLocalized :
    IsLocalizedModule (.powers (algebraMap R (Localization.Away f) g))
      (restriction f g hf L) := by
  let localizationOnChart := toSections_isLocalized (R := CommRingCat.of (Localization.Away f))
    (L.restrict (chart U f hf)) (algebraMap R (Localization.Away f) g)
  exact IsLocalizedModule.of_linearEquiv _
    (toSections (L.restrict (chart U f hf)) (algebraMap R (Localization.Away f) g))
    (overlapLinear f g hf L)

/-- Over the original ring, actual restriction is localization at powers of `g`. -/
instance restrictionBase_isLocalized :
    IsLocalizedModule (.powers g) ((restriction f g hf L).restrictScalars R) :=
  IsLocalizedModule.restrictScalars_powers g (restriction f g hf L)

/-- Every actual overlap section has a denominator which is a power of `g`. -/
lemma exists_denominator (y : overlapSections f g hf L) :
    ∃ (n : ℕ) (x : sourceSections f hf L),
      L.presheaf.map (homOfLE (chart_product_le U f g hf)).op x = g ^ n • y := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ :=
    IsLocalizedModule.surj (.powers g) ((restriction f g hf L).restrictScalars R) y
  exact ⟨n, x, (restriction_apply f g hf L x).symm.trans hx.symm⟩

/-- Vanishing after actual restriction is detected by a power of `g` on the source. -/
lemma restriction_eq_zero_iff (x : sourceSections f hf L) :
    L.presheaf.map (homOfLE (chart_product_le U f g hf)).op x = 0 ↔
      ∃ n : ℕ, g ^ n • x = 0 := by
  rw [← restriction_apply]
  change ((restriction f g hf L).restrictScalars R) x = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (.powers g)]
  simp only [Submonoid.smul_def, Submonoid.mem_powers_iff, Subtype.exists,
    exists_prop, exists_exists_eq_and]

end FLT.Mazur.PrincipalSubmoduleSectionLocalization
