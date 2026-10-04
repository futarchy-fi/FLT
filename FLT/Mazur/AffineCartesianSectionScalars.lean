/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionBaseChange
public import FLT.Mazur.PushoutModuleScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Section scalars in an affine cartesian square

For an actual affine cartesian square, extension from the base identifies with
the sections of the actual sheaf pullback. The formula and restriction theorem
keep the structural morphisms of the square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineCartesianSectionScalars
open AffineModuleGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{u}} [IsAffine X] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

/-- Base scalars on the global sections of a module sheaf. -/
abbrev baseSections {Y Z : Scheme.{u}} (a : Y ⟶ Z) (N : Y.Modules) : ModuleCat Γ(Z, ⊤) :=
  (ModuleCat.restrictScalars a.appTop.hom).obj ((sections Y).obj N)

/-- The affine cartesian section comparison over the base ring. -/
def sectionsIso :
    (ModuleCat.extendScalars g.appTop.hom).obj (baseSections f M) ≅
      baseSections q ((pullback p).obj M) := by
  have : IsAffine P := IsAffine.of_isPullback h
  exact PushoutModuleScalars.scalarIso f.appTop g.appTop p.appTop q.appTop
      (isPushout_appTop_of_isPullback h) ((sections X).obj M) ≪≫
    (ModuleCat.restrictScalars q.appTop.hom).mapIso
      (AffineQuasiCoherentBaseChange.sectionsIso p M)

/-- The comparison is exactly multiplication by the pulled-back base scalar. -/
lemma sectionsIso_tmul (b : Γ(T, ⊤)) (m : Γ(M, ⊤)) :
    (sectionsIso h M).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      q.appTop b • (show Γ((pullback p).obj M, ⊤) from
        ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ m) := by
  have : IsAffine P := IsAffine.of_isPullback h
  change (AffineQuasiCoherentBaseChange.sectionsIso p M).hom
    ((PushoutModuleScalars.scalarIso f.appTop g.appTop p.appTop q.appTop
      (isPushout_appTop_of_isPullback h) ((sections X).obj M)).hom _) = _
  rw [PushoutModuleScalars.scalarIso_tmul]
  exact AffineQuasiCoherentBaseChange.sectionsIso_tmul p M _ m

/-- Restriction of a cartesian base-change tensor uses the actual local sheaf comparison. -/
lemma sectionsIso_restrict (U : X.Opens) (b : Γ(T, ⊤)) (m : Γ(M, ⊤)) :
    ((pullback p).obj M).presheaf.map
      ((TopologicalSpace.Opens.map p.base).map U.leTop).op
      ((sectionsIso h M).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) =
    ModuleSectionBaseChange.comparison p M U
      ((P.presheaf.map ((TopologicalSpace.Opens.map p.base).map U.leTop).op (q.appTop b))
        ⊗ₜ[Γ(X, U),(p.app U).hom] (M.presheaf.map U.leTop.op m)) := by
  have : IsAffine P := IsAffine.of_isPullback h
  have he : (sectionsIso h M).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      ModuleSectionBaseChange.comparison p M ⊤
        ((q.appTop b) ⊗ₜ[Γ(X, ⊤),p.appTop.hom] m) := by
    rw [sectionsIso_tmul, ModuleSectionBaseChange.comparison_tmul]
  rw [he]
  exact ModuleSectionBaseChange.comparison_restrict p M U.leTop (q.appTop b) m

end FLT.Mazur.AffineCartesianSectionScalars
