/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundle
public import FLT.Mazur.IdealModuleSheaf

/-!
# Local triviality of Cartier ideal sheaves

A regular local equation trivializes the actual ideal sheaf on its chart, as an
object of the category of modules on the open subscheme. This supplies the
negative divisor's local rank-one property. The sheaf dual and its comparison
with the positive divisor chart modules are separate constructions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}}

/-- A module sheaf is locally free of rank one if it is locally isomorphic to
the structure module in the category of modules on each open subscheme. -/
def LocallyFreeRankOne (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ structureModule U.toScheme)

/-- Local rank one is invariant under isomorphisms of module sheaves. -/
theorem LocallyFreeRankOne.of_iso {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (e : M ≅ N) : LocallyFreeRankOne N := by
  intro x
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM x
  exact ⟨U, hxU, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eU⟩⟩

/-- The structure module is locally free of rank one on every scheme. -/
theorem structureModule_locallyFreeRankOne : LocallyFreeRankOne (structureModule X) := by
  intro x
  exact ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

/-- A section on an open induces a morphism from its structure module. -/
def sectionHom (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    structureModule U.toScheme ⟶ M.restrict U.ι :=
  (SheafOfModules.unitHomEquiv _).symm <|
    PresheafOfModules.sectionsMk
      (fun V ↦ M.presheaf.map (homOfLE (U.ι_image_le V.unop)).op s)
      (fun V W f ↦ by
        change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
        rw [← M.presheaf.map_comp]
        rfl)

/-- The section morphism is multiplication by the restricted section. -/
lemma sectionHom_app (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) :
    (sectionHom M U s).app V r =
      ((M.restrict U.ι).smul r).hom (M.presheaf.map (homOfLE (U.ι_image_le V)).op s) := rfl

/-- The chosen regular equation, lifted to an actual section of the ideal module. -/
def CartierChart.idealSection {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) : Γ(idealModule I, U.1) :=
  (idealModuleAffineEquiv I U).symm (hU.idealEquiv 1)

/-- Multiplication by the chosen regular equation as a morphism of sheaves. -/
def CartierChart.idealTrivializationHom {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) :
    structureModule U.1.toScheme ⟶ (idealModule I).restrict U.1.ι :=
  sectionHom (idealModule I) U.1 hU.idealSection

/-- On an affine subchart this morphism multiplies by the restricted equation. -/
lemma CartierChart.idealTrivializationHom_apply {I : X.IdealSheafData}
    {U : X.affineOpens} (hU : CartierChart I U) (V : U.1.toScheme.affineOpens)
    (r : Γ(U.1.toScheme, V.1)) :
    idealModuleAffineEquiv I ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩
      (hU.idealTrivializationHom.app V.1 r) =
        CartierModule.idealEquiv _ _
          (regular_restrict (U := ⟨_, V.2.image_of_isOpenImmersion U.1.ι⟩)
            (V := U) (U.1.ι_image_le V.1) hU.choose_spec.1)
          (ideal_eq_span_restrict I (U.1.ι_image_le V.1) hU.choose_spec.2)
            ((U.1.ι.appIso V.1).inv r) := by
  apply Subtype.ext
  rw [idealModuleAffineEquiv_val]
  dsimp only [idealTrivializationHom]
  rw [sectionHom_app]
  have hs : (((idealModule I).restrict U.1.ι).smul r).hom
      ((idealModule I).presheaf.map (homOfLE (U.1.ι_image_le V.1)).op hU.idealSection) =
      ((idealModule I).smul ((U.1.ι.appIso V.1).inv r)).hom
        ((idealModule I).presheaf.map (homOfLE (U.1.ι_image_le V.1)).op hU.idealSection) :=
    (idealModule I).smul_restrictAppIso_hom_apply U.1.ι V.1 r _
  rw [hs]
  erw [Scheme.Modules.Hom.app_smul]
  erw [← idealModuleAffineEquiv_val I
    ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩]
  rw [idealModuleAffineEquiv_restrict I
    (show (⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) ≤ U from
      U.1.ι_image_le V.1)]
  simp only [idealSection, LinearEquiv.apply_symm_apply]
  erw [idealRestrict_val]
  simp [CartierChart.idealEquiv]

/- The sheaf condition promotes the affine calculation to a sheaf isomorphism. -/
instance CartierChart.idealTrivializationHom_isIso {I : X.IdealSheafData}
    {U : X.affineOpens} (hU : CartierChart I U) : IsIso hU.idealTrivializationHom := by
  let φ := (SheafOfModules.toSheaf U.1.toScheme.ringCatSheaf).map
    hU.idealTrivializationHom
  have hφ : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun V : U.1.toScheme.affineOpens ↦ V.1)
      (by simpa using U.1.toScheme.isBasis_affineOpens)
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := CartierModule.idealEquiv _ _
      (regular_restrict (U := ⟨_, V.2.image_of_isOpenImmersion U.1.ι⟩)
        (V := U) (U.1.ι_image_le V.1) hU.choose_spec.1)
      (ideal_eq_span_restrict I (U.1.ι_image_le V.1) hU.choose_spec.2)
    have he : Function.Bijective (fun r ↦
        idealModuleAffineEquiv I
          ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩
          (hU.idealTrivializationHom.app V.1 r)) := by
      change Function.Bijective (fun r : Γ(U.1.toScheme, V.1) ↦ _)
      simp only [hU.idealTrivializationHom_apply]
      exact e.bijective.comp (ConcreteCategory.bijective_of_isIso (U.1.ι.appIso V.1).inv)
    exact (Function.Bijective.of_comp_iff'
      (idealModuleAffineEquiv I
        ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩).bijective _).mp he
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro V
  exact inferInstanceAs (IsIso (φ.hom.app (op V)))

/-- A Cartier equation gives an isomorphism of module sheaves on the whole chart. -/
def CartierChart.idealTrivialization {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) :
    (idealModule I).restrict U.1.ι ≅ structureModule U.1.toScheme :=
  (asIso hU.idealTrivializationHom).symm

/-- The ideal sheaf of an effective Cartier divisor is locally free of rank one. -/
theorem EffectiveCartier.idealModule_locallyFreeRankOne {I : X.IdealSheafData}
    (hI : EffectiveCartier I) : LocallyFreeRankOne (idealModule I) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hI x
  exact ⟨U.1, hxU, ⟨CartierChart.idealTrivialization hU⟩⟩

end FLT.Mazur.FCurve
