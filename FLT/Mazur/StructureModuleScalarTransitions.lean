/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleHomTrivialOpen
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Scalar transition isomorphisms of trivial line sheaves

Units of the actual global section ring give invertible module morphisms.
Composition and arbitrary scheme pullback retain multiplication of the original
functions. These laws support gluing a line from determinant transition units.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.StructureModuleScalarTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve
universe u
variable {X Y : Scheme.{u}}

/-- Multiplication by a global function on the structure-module sheaf. -/
abbrev scalar (s : Γ(X, ⊤)) : structureModule X ⟶ structureModule X :=
  globalSectionHom (structureModule X) s

/-- The scalar map has its literal multiplication action on global sections. -/
theorem scalar_top (s t : Γ(X, ⊤)) : (scalar s).app ⊤ t = t * s := by
  change t • ((structureModule X).presheaf.map (𝟙 (Opposite.op ⊤)) s) = t * s
  rw [(structureModule X).presheaf.map_id]
  rfl

/-- Scalar sheaf maps compose by multiplication of their original functions. -/
@[reassoc] theorem scalar_comp (s t : Γ(X, ⊤)) : scalar s ≫ scalar t = scalar (s * t) := by
  apply globalSection_hom_ext
  change (scalar t).app ⊤ ((scalar s).app ⊤ (1 : Γ(X, ⊤))) = _
  rw [globalSectionHom_top, scalar_top, globalSectionHom_top]

/-- A unit supplies an actual isomorphism of the trivial line sheaf. -/
def scalarIso (s : Γ(X, ⊤)ˣ) : structureModule X ≅ structureModule X where
  hom := scalar (s : Γ(X, ⊤))
  inv := scalar (↑s⁻¹ : Γ(X, ⊤))
  hom_inv_id := by rw [scalar_comp, Units.mul_inv]; exact globalSectionHom_structure_one
  inv_hom_id := by rw [scalar_comp, Units.inv_mul]; exact globalSectionHom_structure_one

/-- Pulling a scalar morphism back multiplies by the pulled-back function. -/
@[reassoc] theorem scalar_pullback (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (pullback f).map (scalar s) ≫ (modulePullbackUnitIso f).hom =
      (modulePullbackUnitIso f).hom ≫ scalar (f.appTop s) := by
  apply (cancel_epi (modulePullbackUnitIso f).inv).mp
  apply globalSection_hom_ext
  change (modulePullbackUnitIso f).hom.app ⊤
      (((pullback f).map (scalar s)).app ⊤
        ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)))) = _
  rw [← pullGlobal_hom, globalSectionHom_top, pullGlobal_structure_coordinate]
  have h := congrArg (fun k ↦ k.app ⊤ (1 : Γ(X, ⊤)))
    (modulePullbackUnitIso f).inv_hom_id
  change (modulePullbackUnitIso f).hom.app ⊤
    ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) at h
  change f.appTop s = (scalar (f.appTop s)).app ⊤ _
  exact ((congrArg ((scalar (f.appTop s)).app ⊤) h).trans
    (globalSectionHom_top (structureModule X) (f.appTop s))).symm

/-- Path normalization preserves the canonical trivial-line comparison. -/
@[reassoc] theorem comparison_unit {Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (SheafPullbackPathComparison.comparison f g k h).hom.app (structureModule Z) ≫
        (modulePullbackUnitIso k).hom =
      (pullback f).map (modulePullbackUnitIso g).hom ≫ (modulePullbackUnitIso f).hom := by
  subst k
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Iso.trans_hom, NatTrans.comp_app] using
      (modulePullbackUnitIso_comp_hom f g).symm

/-- Transport a scalar between two canonically trivialized pullbacks. -/
def coordinateIso {Z : Scheme.{u}} (a : X ⟶ Y) (b : X ⟶ Z)
    (s : Γ(X, ⊤)ˣ) :
    (pullback a).obj (structureModule Y) ≅ (pullback b).obj (structureModule Z) :=
  modulePullbackUnitIso a ≪≫ scalarIso s ≪≫ (modulePullbackUnitIso b).symm

/-- Trivialized scalar transitions compose by their actual unit product. -/
@[reassoc] theorem coordinateIso_comp {Z W : Scheme.{u}}
    (a : X ⟶ Y) (b : X ⟶ Z) (c : X ⟶ W) (s t : Γ(X, ⊤)ˣ) :
    (coordinateIso a b s).hom ≫ (coordinateIso b c t).hom =
      (coordinateIso a c (s * t)).hom := by
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, scalarIso, Category.assoc,
    Iso.inv_hom_id_assoc, scalar_comp_assoc, Units.val_mul]

/-- Refining a trivialization and then forgetting it is the same as forgetting it first. -/
@[reassoc] theorem comparison_inv_unit {Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (pullback f).map (modulePullbackUnitIso g).inv ≫
        (SheafPullbackPathComparison.comparison f g k h).hom.app (structureModule Z) ≫
          (modulePullbackUnitIso k).hom = (modulePullbackUnitIso f).hom := by
  rw [comparison_unit, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Refined scalar coordinates commute with the full pullback path comparison. -/
@[reassoc] theorem coordinateIso_refine {T Z W : Scheme.{u}}
    (f : X ⟶ T) (a : T ⟶ Z) (b : T ⟶ W) (a' : X ⟶ Z) (b' : X ⟶ W)
    (ha : f ≫ a = a') (hb : f ≫ b = b') (s : Γ(T, ⊤)ˣ) (t : Γ(X, ⊤)ˣ)
    (hst : f.appTop (s : Γ(T, ⊤)) = (t : Γ(X, ⊤))) :
    (pullback f).map (coordinateIso a b s).hom ≫
        (SheafPullbackPathComparison.comparison f b b' hb).hom.app (structureModule W) =
      (SheafPullbackPathComparison.comparison f a a' ha).hom.app (structureModule Z) ≫
        (coordinateIso a' b' t).hom := by
  apply (cancel_mono (modulePullbackUnitIso b').hom).mp
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, scalarIso, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, comparison_inv_unit]
  rw [scalar_pullback, hst, ← Category.assoc, ← comparison_unit f a a' ha]
  simp only [Category.assoc]

end FLT.Mazur.StructureModuleScalarTransitions
