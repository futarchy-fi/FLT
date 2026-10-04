/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalSectionBaseChange
public import FLT.Mazur.ModuleTensorPowerSection
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Flat base change in every section-algebra degree

Compose flat global-section base change with the actual tensor-power
pullback comparison. The target is sections of powers of the pulled-back
line bundle, with scalars from the new affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
namespace FLT.Mazur.LinePowerSectionBaseChange
open FCurve ModuleLineBundleTensorPullback OpenModuleSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- Sections of a module isomorphism retain the actual structural base scalars. -/
def openSectionsIso {Y B : Scheme} (a : Y ⟶ B) {M N : Y.Modules}
    (e : M ≅ N) (U : Y.Opens) : openSections a M U ≅ openSections a N U :=
  (ModuleCat.restrictScalars ((Y.presheaf.map U.leTop.op).hom.comp a.appTop.hom)).mapIso
    ((PresheafOfModules.evaluation _ (op U)).mapIso
      ((SheafOfModules.forget _).mapIso e))

/-- Tensor-power comparison on sections over the new base. -/
def powerSectionsIso (n : ℕ) :
    openSections q ((pullback p).obj (tensorPower L n)) ⊤ ≅
      openSections q (tensorPower ((pullback p).obj L) n) ⊤ :=
  openSectionsIso q (tensorPowerIso p L n) ⊤

/-- Flat affine base change of the full space of sections in degree `n`. -/
def degreeIso (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤) ≅
      openSections q (tensorPower ((pullback p).obj L) n) ⊤ := by
  have := (hL.tensorPower n).isFinitePresentation
  exact FlatGlobalSectionBaseChange.sectionsIso h (tensorPower L n) ≪≫
    powerSectionsIso L n

/-- The degree comparison takes a pure scalar tensor to the canonical pulled-back section. -/
lemma degreeIso_tmul (n : ℕ) (b : Γ(T, ⊤)) (s : Γ(tensorPower L n, ⊤)) :
    (degreeIso h L hL n).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      b • (show openSections q (tensorPower ((pullback p).obj L) n) ⊤ from
        (tensorPowerIso p L n).hom.app ⊤ (pullGlobal p (tensorPower L n) s)) := by
  have := (hL.tensorPower n).isFinitePresentation
  change (powerSectionsIso L n).hom
    ((FlatGlobalSectionBaseChange.sectionsIso h (tensorPower L n)).hom
      (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s)) = _
  rw [FlatGlobalSectionBaseChange.sectionsIso_tmul, _root_.map_smul]
  rfl

/-- Pure powers are preserved in every degree, including the unit degree. -/
lemma degreeIso_power (n : ℕ) (b : Γ(T, ⊤)) (s : Γ(L, ⊤)) :
    (degreeIso h L hL n).hom
      (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] tensorPowerSection L ⊤ s n) =
      b • (show openSections q (tensorPower ((pullback p).obj L) n) ⊤ from
        tensorPowerSection ((pullback p).obj L) ⊤ (pullGlobal p L s) n) := by
  rw [degreeIso_tmul, tensorPowerSection_pullback]

end FLT.Mazur.LinePowerSectionBaseChange
