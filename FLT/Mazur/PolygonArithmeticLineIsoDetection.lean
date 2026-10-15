/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticClosedSpecialization
public import FLT.Mazur.PolygonArithmeticCompleteLineQuotient
public import FLT.Mazur.LineBundleSectionOpenPullback
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# Original closed-stage detection of complete line isomorphisms

A morphism between actual line bundles is invertible wherever its closed
restriction is invertible: properness over the local base detects the cover
by the isomorphism open. No inverse morphism is assumed in the input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Closed-stage restrictions detect covers on the original proper arithmetic family. -/
theorem completeOpenCover_of_originalZero {ι : Type*}
    (U : ι → (exactVeroneseProj A π n h hne hgen).Opens)
    (hU : (⨆ i, originalStageToCompatibleProj A π hne hgen n h 0 ⁻¹ᵁ U i) = ⊤) :
    iSup U = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, hy⟩ := exists_completeClosedFiber_specialization A π hne hgen n h y
  have hx : residueFiberInclusion A π (parameter_residue_zero A π hgen) 0 n h x ∈
      ⨆ i, originalStageToCompatibleProj A π hne hgen n h 0 ⁻¹ᵁ U i := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨i, hy.mem_open (U i).isOpen hi⟩

/-- An open containing the entire original zero stage is the entire complete family. -/
theorem completeOpen_eq_top_of_originalZero (U : (exactVeroneseProj A π n h hne hgen).Opens)
    (hU : originalStageToCompatibleProj A π hne hgen n h 0 ⁻¹ᵁ U = ⊤) : U = ⊤ := by
  have hc := completeOpenCover_of_originalZero A π hne hgen n h (fun _ : Unit ↦ U)
    (by simpa only [iSup_const] using hU)
  simpa only [iSup_const] using hc

/-- A complete line morphism is invertible if its actual original zero-stage pullback is. -/
theorem completeLineHom_isIso_of_originalZero
    {L M : (exactVeroneseProj A π n h hne hgen).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a : L ⟶ M)
    [IsIso ((pullback (originalStageToCompatibleProj A π hne hgen n h 0)).map a)] : IsIso a := by
  have hopen : moduleHomIsoOpen a = ⊤ := by
    apply completeOpen_eq_top_of_originalZero A π hne hgen n h
    rw [← moduleHomIsoOpen_pullback a hL hM]
    exact top_unique (le_moduleHomIsoOpen _ ⊤)
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover a
    (fun _ : Unit ↦ moduleHomIsoOpen a)
  · intro x
    exact ⟨(), by rw [hopen]; trivial⟩
  · intro _
    infer_instance

end FLT.Mazur.PolygonArithmeticStages
