/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSerreAffineAcyclic
public import FLT.Mazur.RelativeVeryAmpleLineBundle
public import FLT.Mazur.OpenDirectImageRestriction
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Relative Serre vanishing

A finite affine cover gives one maximum of the affine Serre bounds. Higher
images commute with open restriction, and their vanishing is detected locally.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.OpenSheafRestriction
open FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace FLT.Mazur.ProjectiveSpace

/-- Open restriction commutes with actual abelian higher direct images. -/
def higherImageRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) (q : ℕ) :
    (restriction U).obj
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived q).obj A) ≅
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base).rightDerived q).obj
        ((restriction (f ⁻¹ᵁ U)).obj A) := by
  let I := injectiveResolution A
  let K := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  exact (restriction U).mapIso (I.isoRightDerivedObj _ q) ≪≫
    ((K.sc q).mapHomologyIso (restriction U)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((NatIso.mapHomologicalComplex (OpenDirectImageRestriction.pushforwardRestriction f U)
        (.up ℕ)).app I.cocomplex) ≪≫
    ((OpenDirectImageRestriction.sourceResolution f U A).isoRightDerivedObj
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base) q).symm

/-- Vanishing of a sheaf is detected on any open cover. -/
theorem isZero_of_openCover {Y : Scheme.{u}} (A : TopCat.Sheaf AddCommGrpCat.{u} Y.toTopCat)
    {ι : Type*} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hA : ∀ i, IsZero ((restriction (U i)).obj A)) : IsZero A := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero A).mpr
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hz := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hi⟩ : U i)).map_isZero
    ((sheafToPresheaf _ _).map_isZero (hA i))
  exact hz.of_iso (restrictionPresheafStalkIso (U i) A.obj ⟨x, hi⟩)

/-- Actual module acyclicity is local on the target. -/
theorem modulePushforwardAcyclic_of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    {ι : Type*} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hM : ∀ i, ModulePushforwardAcyclic (f ∣_ U i) (M.restrict (f ⁻¹ᵁ U i).ι)) :
    ModulePushforwardAcyclic f M := by
  intro q
  apply ModuleDerivedAbelianComparison.isZero_module_of_abelian
  apply isZero_of_openCover _ U hU
  intro i
  exact (modulePushforwardAcyclic_abelian _ _ (hM i) q).of_iso
    (higherImageRestrictionIso f (U i) (moduleAbelianSheaf M) (q + 1))

/-- A relatively very ample line has one Serre bound over a compact locally Noetherian base. -/
theorem relativeVeryAmple_eventually_acyclic {X Y : Scheme}
    [IsLocallyNoetherian Y] [CompactSpace Y] (f : X ⟶ Y) (L : X.Modules)
    (D : RelativeVeryAmple f L) :
    ∃ N : ℕ, ∀ n ≥ N, ModulePushforwardAcyclic f (tensorPower L n) := by
  classical
  obtain ⟨s, hs, hfin, hcover⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact
    (U := ⊤) isCompact_univ
  let := hfin.fintype
  have hlocal : ∀ U : s, ∃ N : ℕ, ∀ n ≥ N,
      ModulePushforwardAcyclic (f ∣_ U.val) (tensorPower (L.restrict (f ⁻¹ᵁ U.val).ι) n) := by
    intro U
    have hU : IsAffineOpen U.val := hs U.property
    let := IsLocallyNoetherian.component_noetherian ⟨U.val, hU⟩
    let p := (D U.val hU).some
    exact exists_affine_line_power_acyclic_of_iso (f ∣_ U.val) hU.isoSpec
      p.embedding p.over _ (AffineLineCoefficients.ofIso p.embedding p.coefficientIso)
  choose N hN using hlocal
  refine ⟨Finset.univ.sup N, fun n hn ↦ ?_⟩
  apply modulePushforwardAcyclic_of_openCover f _ (fun U : s ↦ U.val)
  · rw [iSup_subtype, ← sSup_eq_iSup, ← hcover]
  · intro U q
    have hNU : N U ≤ n := le_trans (Finset.le_sup (Finset.mem_univ U)) hn
    exact (hN U n hNU q).of_iso
      (((Scheme.Modules.pushforward (f ∣_ U.val)).rightDerived (q + 1)).mapIso
        (tensorPowerRestrictIso L (f ⁻¹ᵁ U.val).ι n))

end FLT.Mazur.ProjectiveSpace
