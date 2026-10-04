/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonIdealModulePullback
public import FLT.Mazur.PolygonDivisorPowerPullback
public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.ModuleGlobalSectionPullback
public import FLT.Mazur.ProjectiveLineMarkedPullbackCoordinates
/-!
# Direct comparison of polygon divisor powers

Apply the torus and divisor-complement cover to the powered ideal itself.
Duality then gives a component comparison preserving the canonical section,
without passing through the tensor-power isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonDirectPowerComparison
open PolygonPinching PolygonMarkedSections FCurve PolygonDivisorNormalizationPullback
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The canonical ideal comparison is invertible for every boundary divisor power. -/
theorem comparison_isIso (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    IsIso (idealModulePullbackHom (PolygonBoundaryDivisor.ideal K n p a ^ m)
      (componentι K n i ≫ p).left) := by
  let I := PolygonBoundaryDivisor.ideal K n p a ^ m
  let f := (componentι K n i ≫ p).left
  let t := (torusToComponent K).left
  let j := (torusToComponent K ≫ componentι K n i ≫ p).left
  let := torus_isOpenImmersion K n hn p q h i
  have ht : IsIso ((Scheme.Modules.restrictFunctor t).map (idealModulePullbackHom I f)) :=
    idealModulePullbackHom_isIso_restrict I f (𝟙 _) t j (by simp [f, t, j])
  have hr := moduleHom_isIso_restrict_opensRange (idealModulePullbackHom I f) t
  have hc := idealModulePullbackHom_offSupport I f
  let U : Bool → (ProjectiveLine.scheme K).Opens :=
    fun b ↦ if b then f ⁻¹ᵁ I.support.compl else t.opensRange
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (idealModulePullbackHom I f) U
  · intro z
    rcases PolygonIdealModulePullback.cover K n hn p q h a i z with hz | hz
    · exact ⟨false, hz⟩
    · refine ⟨true, ?_⟩
      change f z ∉ I.support
      cases m with
      | zero => simpa only [I, pow_zero, Scheme.IdealSheafData.one_eq_top,
          Scheme.IdealSheafData.support_top] using
          (show f z ∉ (⊥ : TopologicalSpace.Closeds C.left) from fun h ↦ h)
      | succ m => exact hz
  · intro b
    cases b
    · exact hr
    · exact hc

/-- Direct duality identifies each pulled-back divisor power with the marked power. -/
def lineIso (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a ^ m)
        ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)) ≅
      divisorLineBundle ((markedPoint K (a i)).ker ^ m)
        ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow m) := by
  letI := comparison_isIso K n hn p q h a i m
  exact divisorLinePullbackIsoOfEq (componentι K n i ≫ p).left
    ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)
    ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow m)
    (PolygonDivisorPowerPullback.normalization K n hn p q h a i m)

/-- The direct comparison preserves the canonical section for every multiplicity. -/
lemma lineIso_section (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (lineIso K n hn p q h a i m).hom.app ⊤
      (pullGlobal (componentι K n i ≫ p).left _
        (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m) ⊤)) =
      divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow m) ⊤ := by
  let := comparison_isIso K n hn p q h a i m
  rw [divisorSection, pullGlobal_hom]
  exact divisorLinePullbackIsoOfEq_section_apply _ _ _ _ ⊤
end FLT.Mazur.PolygonDirectPowerComparison
