/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# Dual-ideal section coordinates on a marked affine chart

The actual section ideal and all its powers have explicit regular equations.
Evaluation at these generators gives coordinates on genuine divisor-sheaf
sections. The canonical section evaluates at zero to the unit (-a)^m.
-/

open CategoryTheory AlgebraicGeometry Polynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedCharts FCurve
variable (K : Type u) [Field K]

/-- The whole affine coordinate chart, as an affine open. -/
abbrev chartTop : (ProjectiveLine.chart K).affineOpens := ⟨⊤, isAffineOpen_top _⟩
/-- The canonical identification of polynomials with chart global functions. -/
def coordinateRing : K[X] ≃+* Γ(ProjectiveLine.chart K, ⊤) :=
  (Scheme.ΓSpecIso (.of K[X])).symm.commRingCatIsoToRingEquiv

/-- The actual global function X minus the marked coordinate. -/
def equation (a : K) : Γ(ProjectiveLine.chart K, ⊤) := coordinateRing K (X - C a)

/-- The affine marked-point ideal has the stated principal equation. -/
theorem ideal_equation (a : K) :
    (chartPoint K a).ker.ideal (chartTop K) = Ideal.span {equation K a} := by
  have he := congrArg (Ideal.map (coordinateRing K).toRingHom) (chart_ideal K a)
  change Ideal.map (coordinateRing K)
    (Ideal.comap (coordinateRing K) ((chartPoint K a).ker.ideal (chartTop K))) = _ at he
  rw [Ideal.map_comap_of_surjective _ (coordinateRing K).surjective,
    Ideal.map_span, Set.image_singleton] at he
  exact he

/-- The coordinate equation is regular in the actual global section ring. -/
theorem equation_regular (a : K) : IsRegular (equation K a) := by
  have hr := (monic_X_sub_C a).isRegular
  constructor
  · intro x y hh
    apply (coordinateRing K).symm.injective
    apply hr.left
    simpa only [equation, map_mul, RingEquiv.symm_apply_apply] using
      congrArg (coordinateRing K).symm hh
  · intro x y hh
    apply (coordinateRing K).symm.injective
    apply hr.right
    simpa only [equation, map_mul, RingEquiv.symm_apply_apply] using
      congrArg (coordinateRing K).symm hh

/-- The whole affine chart is a Cartier chart for the marked ideal. -/
theorem chart_cartier (a : K) : CartierChart (chartPoint K a).ker (chartTop K) :=
  ⟨equation K a, equation_regular K a, ideal_equation K a⟩

/-- The marked affine section is an effective Cartier divisor. -/
theorem effectiveCartier (a : K) : EffectiveCartier (chartPoint K a).ker :=
  fun _ ↦ ⟨chartTop K, trivial, chart_cartier K a⟩

/-- Every ideal power has the corresponding power of the regular equation. -/
theorem power_equation (a : K) (m : ℕ) :
    ((chartPoint K a).ker ^ m).ideal (chartTop K) = Ideal.span {equation K a ^ m} := by
  change ((chartPoint K a).ker.ideal (chartTop K)) ^ m = _
  rw [ideal_equation, Ideal.span_singleton_pow]

/-- Coordinates on genuine sections of the dual of the powered ideal. -/
def sectionsCoordinate (a : K) (m : ℕ) :
    Γ(divisorLineBundle ((chartPoint K a).ker ^ m) ((effectiveCartier K a).pow m), ⊤) ≃ₗ[
      Γ(ProjectiveLine.chart K, ⊤)] Γ(ProjectiveLine.chart K, ⊤) :=
  (show CartierChart ((chartPoint K a).ker ^ m) (chartTop K) from
    ⟨equation K a ^ m, (equation_regular K a).pow m, power_equation K a m⟩).divisorSectionsEquiv
      ((effectiveCartier K a).pow m) ≪≫ₗ
    CartierModule.dualEquiv _ _ ((equation_regular K a).pow m) (power_equation K a m)

/-- The canonical section has coordinate equal to the powered equation. -/
theorem canonicalSection_coordinate (a : K) (m : ℕ) :
    sectionsCoordinate K a m (divisorSection ((effectiveCartier K a).pow m) ⊤) =
      equation K a ^ m := by
  change divisorChartEval _ (chartTop K) (divisorSection _ ⊤)
    (CartierModule.idealEquiv _ _ _ _ 1) = _
  rw [divisorSection_eval]
  exact one_mul _

/-- In polynomial coordinates, the canonical section is the powered linear factor. -/
theorem canonicalSection_polynomial (a : K) (m : ℕ) :
    (coordinateRing K).symm (sectionsCoordinate K a m
      (divisorSection ((effectiveCartier K a).pow m) ⊤)) = (X - C a) ^ m := by
  rw [canonicalSection_coordinate]
  simp [equation]

/-- At coordinate zero the canonical section evaluates to an explicit coefficient unit. -/
theorem canonicalSection_endpoint (a : Kˣ) (m : ℕ) :
    eval 0 ((coordinateRing K).symm (sectionsCoordinate K a m
      (divisorSection ((effectiveCartier K a).pow m) ⊤))) = (↑((-a) ^ m : Kˣ) : K) := by
  rw [canonicalSection_polynomial]
  simp
end FLT.Mazur.ProjectiveLineMarkedDualCoordinates
