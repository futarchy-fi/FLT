/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectivePointSmooth
public import FLT.Mazur.WeierstrassPartialFieldPointComparison

/-!
# Relative smooth outputs for arbitrary coefficient equations

Nonsingular residue-field inputs force each original addition-chart morphism
to land in the actual relative smooth locus. The source algebra may be
nonreduced, and the coefficients may vary without a unit discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (i : AdditionChartIndex)

/-- All original field-valued addition outputs land in the actual relative smooth open. -/
theorem additionFieldPoint_chart_range_smooth
    (f : additionChartRing W i →ₐ[R] K)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (additionInputLeft W i (coord W 2 0))) (f (additionInputLeft W i (coord W 2 1))))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (additionInputRight W i (coord W 2 0))) (f (additionInputRight W i (coord W 2 1)))) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i) ⊆
      integralSmoothOpen W := by
  rw [additionFieldPoint_chart_sum W i f h₁ h₂]
  exact projectiveToIntegral_range_smooth W _

variable {S : Type u} [CommRing S] [Algebra R S]
  (f : additionChartRing W i →ₐ[R] S)
  (hn : ∀ p : PrimeSpectrum S,
    let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
    (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
        (g (additionInputLeft W i (coord W 2 0)))
        (g (additionInputLeft W i (coord W 2 1))) ∧
      (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
        (g (additionInputRight W i (coord W 2 0)))
        (g (additionInputRight W i (coord W 2 1))))

include hn

/-- Residue-field nonsingularity of both inputs proves smooth output over an arbitrary algebra. -/
theorem additionAlgebra_chart_range_smooth :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i) ⊆
      integralSmoothOpen W := by
  rintro _ ⟨p, rfl⟩
  let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
  have hp : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap S p.asIdeal.ResidueField)) := by
    rw [PrimeSpectrum.residueField_comap]
    exact Set.mem_singleton p
  obtain ⟨z, hz⟩ := hp
  have h := additionFieldPoint_chart_range_smooth W i g (hn p).1 (hn p).2
  have he : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ additionCurveChart W i =
      Spec.map (CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hm := h ⟨z, rfl⟩
  rw [he] at hm
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i)
    (PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z) ∈ _ at hm
  rwa [hz] at hm

/-- The original chart output canonically factors through the relative smooth locus. -/
def additionAlgebraToSmooth : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i)
    (by rw [Scheme.Opens.range_ι]; exact additionAlgebra_chart_range_smooth W i f hn)

/-- The smooth factor has exactly the original addition-chart output. -/
@[reassoc] theorem additionAlgebraToSmooth_inclusion :
    additionAlgebraToSmooth W i f hn ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factor preserves the original coefficient map. -/
theorem additionAlgebraToSmooth_structure :
    additionAlgebraToSmooth W i f hn ≫ integralSmoothStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [integralSmoothStructure, ← Category.assoc, additionAlgebraToSmooth_inclusion,
    Category.assoc, additionCurveChart_structure]
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    specAlgHom_structure (additionChartAlgRestriction W i)]
  exact specAlgHom_structure f

end FLT.Mazur.WeierstrassIntegralChart
