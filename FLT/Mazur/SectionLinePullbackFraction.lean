/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLinePullback
public import FLT.Mazur.SectionGradedProjPullbackEvaluation

/-!
# Intrinsic section equations with a specified line comparison

Transporting the actual pulled-back line by an isomorphism preserves the
fraction equation and the generating-section condition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.SectionLinePullbackFraction

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme} (p : Y ⟶ X) (k : Z ⟶ Y) (L : X.Modules) (M : Y.Modules)
  (e : (pullback p).obj L ≅ M)

/-- An equation between transported sections gives the original composite-pullback equation. -/
theorem scalar_equation (d : ℕ) (s t : Γ(tensorPower L d, ⊤)) (a : Γ(Z, ⊤))
    (he : a • pullGlobal k (tensorPower M d) (SectionGradedLinePullback.sectionMap p e d ⊤ s) =
      pullGlobal k (tensorPower M d) (SectionGradedLinePullback.sectionMap p e d ⊤ t)) :
    a • pullGlobal (k ≫ p) (tensorPower L d) s =
      pullGlobal (k ≫ p) (tensorPower L d) t := by
  apply SectionGradedProjPullbackEvaluation.scalar_equation_comp p k L d s t a
  apply (ConcreteCategory.bijective_of_isIso
    (((pullback k).map (tensorPowerCongr e d).hom).app ⊤)).injective
  rw [Hom.app_smul, pullGlobal_naturality, pullGlobal_naturality]
  exact he

/-- A generating original section remains a generator after the specified line comparison. -/
theorem ringHom_isUnit_section
    (c : (pullback k).obj M ≅ structureModule Z)
    (c' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hs : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L c' (of L ⊤ d s))) :
    IsUnit (SectionGradedProjChart.ringHom k M c
      (of M ⊤ d (SectionGradedLinePullback.sectionMap p e d ⊤ s))) := by
  let c'' := (pullback k).mapIso e ≪≫ c
  have hu := SectionGradedProjPullbackEvaluation.ringHom_isUnit_pull_section p k L c'' c' s hs
  have := SectionGradedProjChart.pullGenerator_isIso_of_ringHom k ((pullback p).obj L) c''
    (SectionGradedPullback.pull p L d ⊤ s) hu
  have hj := globalSectionHom_isIso_transport _ ((pullback k).mapIso (tensorPowerCongr e d))
    (pullGlobal k _ (SectionGradedPullback.pull p L d ⊤ s))
  change IsIso (globalSectionHom _
    (((pullback k).map (tensorPowerCongr e d).hom).app ⊤
      (pullGlobal k _ (SectionGradedPullback.pull p L d ⊤ s)))) at hj
  rw [pullGlobal_naturality] at hj
  have : IsIso (globalSectionHom _
    (pullGlobal k (tensorPower M d) (SectionGradedLinePullback.sectionMap p e d ⊤ s))) := hj
  exact SectionGradedProjChart.ringHom_isUnit_of_pullGenerator k M c _

end FLT.Mazur.SectionLinePullbackFraction
