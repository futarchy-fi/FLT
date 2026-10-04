/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Descent from the transition ratios of actual generators

Generator section isomorphisms glue against a unit cocycle when its transition
coefficients are the actual section ratios on every common subopen.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafUnitCocycle FLT.Mazur.ModuleSheafMorphismGluing
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (t : ι → Γ(M, ⊤)) (ht : ∀ i, U i ≤ sectionGeneratorOpen M (t i))
    (g : Cocycle U)
/-- The section map is invertible on every subopen of its generator open. -/
lemma sectionHom_isIso_onGeneratorSubopen (s : Γ(M, ⊤)) (V : X.Opens)
    (hv : V ≤ sectionGeneratorOpen M s) :
    IsIso (sectionHom M V (M.presheaf.map (homOfLE le_top).op s)) := by
  have := (le_moduleHomIsoOpen_iff (globalSectionHom M s) V).mp hv
  rw [sectionHom_restrict_global]
  infer_instance

/-- Compare the cocycle chart with the actual generating section. -/
def sectionCocycleLocalIso (i : ι) :
    g.sheaf.restrict (U i).ι ≅ M.restrict (U i).ι :=
  letI := sectionHom_isIso_onGeneratorSubopen M (t i) (U i) (ht i)
  g.restrictIso i ≪≫ asIso (sectionHom M (U i) (M.presheaf.map (homOfLE le_top).op (t i)))

/-- The local comparison multiplies the coefficient by the generating section. -/
lemma sectionCocycleLocalIso_app (i : ι) (W : (U i).toScheme.Opens)
    (s : g.sections ((U i).ι ''ᵁ W)) :
    (sectionCocycleLocalIso M U t ht g i).hom.app W s =
      g.evaluate i ((U i).ι_image_le W) s •
        M.presheaf.map (homOfLE (show (U i).ι ''ᵁ W ≤ ⊤ from le_top)).op (t i) := by
  change (sectionHom M (U i) (M.presheaf.map (homOfLE le_top).op (t i))).app W
    (g.evaluate i ((U i).ι_image_le W) s) = _
  rw [sectionHom_app]
  erw [M.smul_restrictAppIso_hom_apply (U i).ι W]
  change ((U i).ι.appIso W).inv (g.evaluate i ((U i).ι_image_le W) s) •
    M.presheaf.map _ (M.presheaf.map _ (t i)) = _
  rw [Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv, ← Functor.map_comp_apply]
  rfl

/-- The same formula on every ambient subopen of a chart. -/
lemma sectionCocycleLocalIso_localApp (i : ι) (V : X.Opens) (hv : V ≤ U i)
    (s : g.sections V) :
    localApp ((restrictionEquiv (U i)).symm
      (sectionCocycleLocalIso M U t ht g i).hom) hv s =
      g.evaluate i hv s • M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (t i) := by
  obtain ⟨W, rfl⟩ : ∃ W : (U i).toScheme.Opens, (U i).ι ''ᵁ W = V := by
    refine ⟨(U i).ι ⁻¹ᵁ V, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hv]
  have he := congrArg (fun b ↦ b.app W s)
    ((restrictionEquiv (U i)).apply_symm_apply
      (sectionCocycleLocalIso M U t ht g i).hom)
  exact he.trans (sectionCocycleLocalIso_app M U t ht g i W s)

/-- Matching transition ratios make the actual local comparisons agree. -/
lemma sectionCocycleLocalIso_compatible
    (hg : ∀ i j V hi hj, (g.unit i j V hi hj : Γ(X, V)) =
      sectionRatioOn M (t i) V (hi.trans (ht i)) (t j)) :
    Compatible U (fun i ↦ (restrictionEquiv (U i)).symm
      (sectionCocycleLocalIso M U t ht g i).hom) := by
  intro i j V hi hj
  ext s
  rw [sectionCocycleLocalIso_localApp, sectionCocycleLocalIso_localApp,
    g.transition i j hi hj, hg]
  rw [mul_comm, mul_smul, sectionRatioOn_smul]

/-- A cocycle with the actual section ratios descends to the original module. -/
def sectionCocycleIso (hU : iSup U = ⊤)
    (hg : ∀ i j V hi hj, (g.unit i j V hi hj : Γ(X, V)) =
      sectionRatioOn M (t i) V (hi.trans (ht i)) (t j)) : g.sheaf ≅ M :=
  glueLocalIso U hU (sectionCocycleLocalIso M U t ht g)
    (sectionCocycleLocalIso_compatible M U t ht g hg)
end FLT.Mazur.FCurve
