/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionUnit
public import FLT.Mazur.ModuleGlobalSectionExt

/-!
# Generators after pullback to a unit-coordinate open

Actual sheaf trivializations certify generation from linear section coordinates.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules)
/-- Extend a trivialization on the top open to the original scheme. -/
def trivializationOfTop (e : M.restrict (⊤ : X.Opens).ι ≅ structureModule (⊤ : X.Opens).toScheme) :
    M ≅ structureModule X :=
  (restrictFunctorId.app M).symm ≪≫
    ((restrictFunctorCongr X.toIso_inv_ι).app M).symm ≪≫
    (restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app M ≪≫
    (restrictFunctor X.topIso.inv).mapIso e ≪≫ restrictUnitIso X.topIso.inv

/-- A unit coordinate in an actual sheaf trivialization gives a global generator. -/
lemma globalSectionHom_isIso_of_coordinate (s : Γ(M, ⊤)) (e : M ≅ structureModule X)
    (hs : IsUnit (show Γ(X, ⊤) from e.hom.app ⊤ s)) :
    IsIso (globalSectionHom M s) := by
  have he : globalSectionHom M s ≫ e.hom =
      globalSectionHom (structureModule X) (e.hom.app ⊤ s) := by
    apply globalSection_hom_ext
    simp only [Hom.comp_app, AddCommGrpCat.comp_apply, globalSectionHom_top]
  have hunit (r : Γ(X, ⊤)) (hr : IsUnit r) :
      IsIso (globalSectionHom (structureModule X) r) := by
    apply Hom.isIso_iff_isIso_app.mpr
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun a : Γ(X, U) ↦
      a * X.presheaf.map (homOfLE le_top).op r)
    obtain ⟨v, hv⟩ := hr.map (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
    rw [← hv]
    exact (Units.mulRight v).bijective
  have := hunit _ hs
  have : IsIso (globalSectionHom M s ≫ e.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

/-- Arbitrary linear section coordinates detect a generator of a trivial sheaf. -/
lemma globalSectionHom_isIso_of_linear_coordinate
    (e : M ≅ structureModule X) (c : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤))
    (s : Γ(M, ⊤)) (hs : IsUnit (c s)) : IsIso (globalSectionHom M s) := by
  apply globalSectionHom_isIso_of_coordinate M s e
  let t := e.inv.app ⊤ (1 : Γ(X, ⊤))
  have ht : e.hom.app ⊤ t = (1 : Γ(X, ⊤)) :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) e.inv_hom_id) _
  obtain ⟨v, hv⟩ := hs
  have hst : (c t * (↑v⁻¹ : Γ(X, ⊤))) • s = t := by
    apply c.injective
    rw [c.map_smul, smul_eq_mul, ← hv]
    simp
  have he := congrArg (e.hom.app ⊤) hst
  rw [Hom.app_smul, ht] at he
  exact IsUnit.of_mul_eq_one_right _ he

/-- A unit pulled-back coordinate generates the actual pulled-back sheaf. -/
lemma pullGlobal_isIso_of_unit_coordinate {Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules)
    (e : N ≅ structureModule Y) (c : Γ(N, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (s : Γ(N, ⊤)) (hs : IsUnit (f.appTop (c s))) :
    IsIso (globalSectionHom ((pullback f).obj N) (pullGlobal f N s)) := by
  let t := c.symm 1
  have ht : IsIso (globalSectionHom N t) :=
    globalSectionHom_isIso_of_linear_coordinate N e c t (by simp [t])
  let d := (pullback f).mapIso (asIso (globalSectionHom N t)).symm ≪≫ modulePullbackUnitIso f
  have hd : d.hom.app ⊤ (pullGlobal f N t) = (1 : Γ(X, ⊤)) := by
    rw [← globalSectionHom_top N t, pullGlobal_hom]
    change (((pullback f).map (globalSectionHom N t)) ≫ d.hom).app ⊤
      ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤))) = _
    have hid : (pullback f).map (globalSectionHom N t) ≫ d.hom =
        (modulePullbackUnitIso f).hom := by
      simp [d]
    rw [hid]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.app ⊤) (modulePullbackUnitIso f).inv_hom_id) _
  have hst : (c s) • t = s := by
    apply c.injective
    simp [t]
  apply globalSectionHom_isIso_of_coordinate ((pullback f).obj N) _ d
  rw [← hst, map_smulₛₗ, Hom.app_smul, hd]
  simpa only [smul_eq_mul, mul_one] using hs

/-- Global section morphisms respect actual sheaf morphisms. -/
lemma globalSectionHom_naturality {N : X.Modules} (e : M ⟶ N) (s : Γ(M, ⊤)) :
    globalSectionHom M s ≫ e = globalSectionHom N (e.app ⊤ s) := by
  apply globalSection_hom_ext
  simp only [Hom.comp_app, AddCommGrpCat.comp_apply, globalSectionHom_top]

/-- An actual sheaf isomorphism transports invertibility of the section map. -/
lemma globalSectionHom_isIso_transport {N : X.Modules} (e : M ≅ N) (s : Γ(M, ⊤))
    [IsIso (globalSectionHom M s)] : IsIso (globalSectionHom N (e.hom.app ⊤ s)) := by
  rw [← globalSectionHom_naturality]
  infer_instance

/-- The pulled-back section morphism is the pullback of its original morphism. -/
lemma globalSectionHom_pullGlobal {Y : Scheme.{u}} (f : Y ⟶ X) (s : Γ(M, ⊤)) :
    globalSectionHom ((pullback f).obj M) (pullGlobal f M s) =
      (modulePullbackUnitIso f).inv ≫ (pullback f).map (globalSectionHom M s) := by
  apply globalSection_hom_ext
  rw [globalSectionHom_top, Hom.comp_app, AddCommGrpCat.comp_apply,
    ← pullGlobal_hom, globalSectionHom_top]

end FLT.Mazur.FCurve
