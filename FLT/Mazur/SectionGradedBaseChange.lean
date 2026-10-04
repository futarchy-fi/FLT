/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinePowerSectionBaseChange
public import FLT.Mazur.ScalarExtensionDirectSum
public import FLT.Mazur.SectionGradedSum

/-!
# Flat base change of the full graded section module

The direct sum of all tensor-power sections commutes with flat affine base
change. This is an isomorphism of modules with an explicit homogeneous
formula; upgrading it to an algebra isomorphism requires multiplication
coherence, and is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings
namespace FLT.Mazur.SectionGradedBaseChange
open FCurve ModuleLineBundleTensorPullback OpenModuleSectionScalars LinePowerSectionBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The full graded section module with the original structural base scalars. -/
abbrev sectionModule {Y B : Scheme} (a : Y ⟶ B) (M : Y.Modules) : ModuleCat Γ(B, ⊤) :=
  ModuleCat.of Γ(B, ⊤) (⨁ n : ℕ, openSections a (tensorPower M n) ⊤)

/-- Direct sum of all degree comparisons. -/
def degreeSumIso :
    ModuleCat.of Γ(T, ⊤) (⨁ n : ℕ,
      (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤)) ≅
        sectionModule q ((pullback p).obj L) :=
  (DirectSum.congrLinearEquiv (fun n ↦ (degreeIso h L hL n).toLinearEquiv)).toModuleIso

/-- Flat affine base change commutes with the entire graded section module. -/
def sectionsIso :
    (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L) ≅
      sectionModule q ((pullback p).obj L) :=
  ScalarExtensionDirectSum.comparison g.appTop.hom
    (fun n ↦ openSections f (tensorPower L n) ⊤) ≪≫ degreeSumIso h L hL

/-- On a homogeneous insertion the sum comparison is the degree comparison. -/
lemma degreeSumIso_lof (n : ℕ)
    (s : (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤)) :
    (degreeSumIso h L hL).hom
      (DirectSum.lof Γ(T, ⊤) ℕ (fun n ↦
        (ModuleCat.extendScalars g.appTop.hom).obj (openSections f (tensorPower L n) ⊤)) n s) =
      DirectSum.lof Γ(T, ⊤) ℕ
        (fun n ↦ openSections q (tensorPower ((pullback p).obj L) n) ⊤) n
          ((degreeIso h L hL n).hom s) := by
  change DirectSum.lmap (fun n ↦ (degreeIso h L hL n).hom.hom)
    (DirectSum.lof Γ(T, ⊤) ℕ _ n s) = _
  exact DirectSum.lmap_lof _ _ _

/-- The full comparison preserves degrees and the actual pullback formula. -/
lemma sectionsIso_tmul_lof (n : ℕ) (b : Γ(T, ⊤)) (s : Γ(tensorPower L n, ⊤)) :
    (sectionsIso h L hL).hom
      (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
        DirectSum.lof Γ(S, ⊤) ℕ (fun n ↦ openSections f (tensorPower L n) ⊤) n s) =
      DirectSum.lof Γ(T, ⊤) ℕ
        (fun n ↦ openSections q (tensorPower ((pullback p).obj L) n) ⊤) n
          (b • (show openSections q (tensorPower ((pullback p).obj L) n) ⊤ from
            (tensorPowerIso p L n).hom.app ⊤ (pullGlobal p (tensorPower L n) s))) := by
  change (degreeSumIso h L hL).hom
    ((ScalarExtensionDirectSum.comparison g.appTop.hom _).hom _) = _
  rw [ScalarExtensionDirectSum.comparison_tmul_lof, degreeSumIso_lof, degreeIso_tmul]

end FLT.Mazur.SectionGradedBaseChange
