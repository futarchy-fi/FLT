/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralPointSection
public import FLT.Mazur.EllipticSmoothReduction
public import FLT.Mazur.WeierstrassProjectiveRelativeSmoothCriterion

/-!
# Arithmetic reduction is the actual closed fiber of the integral section

The closed fiber of the constructed section belongs to the geometric smooth
locus exactly when the original point belongs to arithmetic smooth reduction.
The statement includes singular reductions and keeps the original cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The actual residue-field morphism of the original integral section. -/
def integralPointSpecialization (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of (ResidueField A)) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (residue A)) ≫ integralPointSection A W P

/-- Specialization of the section uses the same normalized integral coordinates. -/
theorem integralPointSpecialization_chart
    (P : (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3) (v : Fin 3 → A)
    (hv : W.toProjective.Equation v) (hj : v j = 1)
    (he : (⟦fun i => (v i : K)⟧ : PointClass K) = P.point) :
    integralPointSpecialization A W P = integralChartPoint W j (residue A ∘ v)
      (hv.map (residue A)) (by simp [hj]) := by
  have hv' : (W.map (algebraMap A A)).toProjective.Equation v := by
    simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using hv
  rw [integralPointSpecialization, integralPointSection_chart A W P j v hv' hj he]
  exact integralChartPoint_natural W j v hv' hj (Algebra.ofId A (ResidueField A)) _ _

/-- Arithmetic smooth reduction is smoothness of the actual specialized section. -/
theorem integralPointSpecialization_smooth_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (integralPointSpecialization A W P) ⊆ integralSmoothOpen W ↔
      SmoothReduction A W P := by
  obtain ⟨j, v, hv, hj, he, hr⟩ := exists_normalized_integral_lift A W P
  rw [integralPointSpecialization_chart A W P j v hv hj he]
  change Set.range (Spec.map _ ≫ integralCurveChart W j) ⊆ _ ↔ _
  rw [chartFieldPoint_smooth_iff]
  have hc : (evaluation W j (residue A ∘ v) (hv.map (residue A))
      (by simp [hj])) ∘ coord W j = residue A ∘ v := by
    funext i
    exact evaluation_coord _ _ _ _ _ _
  rw [hc]
  change _ ↔ (W.map (residue A)).toProjective.NonsingularLift (projectiveReduction A W P)
  rw [← hr]
  rfl

/-- The image of the closed source point is the actual arithmetic smooth-reduction test. -/
theorem integralPointSection_closed_smooth_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointSection A W P (closedPoint A) ∈ integralSmoothOpen W ↔
      SmoothReduction A W P := by
  rw [← integralPointSpecialization_smooth_iff]
  constructor
  · intro h
    rintro _ ⟨z, rfl⟩
    change integralPointSection A W P (PrimeSpectrum.comap (residue A) z) ∈ _
    rw [PrimeSpectrum.comap_residue]
    exact h
  · intro h
    have hm := h ⟨closedPoint (ResidueField A), rfl⟩
    change integralPointSection A W P
      (PrimeSpectrum.comap (residue A) (closedPoint (ResidueField A))) ∈ _ at hm
    rw [PrimeSpectrum.comap_residue] at hm
    exact hm

/-- The entire integral section lies in the smooth locus exactly for arithmetic E₀. -/
theorem integralPointSection_range_smooth_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (integralPointSection A W P) ⊆ integralSmoothOpen W ↔
      SmoothReduction A W P := by
  rw [← integralPointSection_closed_smooth_iff]
  constructor
  · exact fun h => h ⟨closedPoint A, rfl⟩
  · intro h
    rintro _ ⟨x, rfl⟩
    exact (specializes_closedPoint x).mem_open
      (integralPointSection A W P ⁻¹ᵁ integralSmoothOpen W).isOpen h

/-- On E₀ the specialized section is precisely the scheme point of arithmetic reduction. -/
theorem integralPointSpecialization_eq_projective
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    integralPointSpecialization A W P =
      (projectiveToIntegral W (smoothReductionPoint A W ⟨P, hP⟩)).left := by
  obtain ⟨j, v, hv, hj, he, hr⟩ := exists_normalized_integral_lift A W P
  rw [integralPointSpecialization_chart A W P j v hv hj he]
  exact (projectiveToIntegral_chart W _ j _ (hv.map (residue A))
    (by simp [hj]) hr).symm

end FLT.Mazur.WeierstrassIntegralChart
