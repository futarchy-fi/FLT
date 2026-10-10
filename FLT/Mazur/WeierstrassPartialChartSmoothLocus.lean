/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPartialAdditionSmoothInputs

/-!
# Actual relative smooth restrictions of all four addition charts

Restrict the original addition charts to the open where both input morphisms
are relatively smooth points. Their output morphisms factor through the full
relative smooth locus, for arbitrary and varying coefficient equations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Relative smoothness at one input point gives its nonsingular residue specialization. -/
theorem affineAlgebra_residue_nonsingular_at (f : Coordinate W 2 →ₐ[R] S)
    (p : PrimeSpectrum S)
    (hp : (Spec.map (CommRingCat.ofHom f.toRingHom)) p ∈ (chartStructure W 2).smoothLocus) :
    let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
    (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
      (g (coord W 2 0)) (g (coord W 2 1)) := by
  let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
  apply affineFieldPoint_nonsingular_of_smooth W g
  have he : Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [he]
  rintro _ ⟨z, rfl⟩
  have hz : PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z = p :=
    Set.mem_singleton_iff.mp ((PrimeSpectrum.residueField_comap p) ▸ Set.mem_range_self z)
  change (Spec.map (CommRingCat.ofHom f.toRingHom))
    (PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z) ∈ _
  rwa [hz]

variable (i : AdditionChartIndex)

/-- The actual open in an addition chart where both original input points are smooth. -/
def additionSmoothInputOpen : (Spec (additionChartRing W i)).Opens :=
  Spec.map (CommRingCat.ofHom (additionInputLeft W i).toRingHom) ⁻¹ᵁ
      (chartStructure W 2).smoothLocus ⊓
    Spec.map (CommRingCat.ofHom (additionInputRight W i).toRingHom) ⁻¹ᵁ
      (chartStructure W 2).smoothLocus

/-- Each original chart sends its entire smooth-input open into the relative smooth locus. -/
theorem additionSmoothInputOpen_output (p : Spec (additionChartRing W i))
    (hp : p ∈ additionSmoothInputOpen W i) :
    additionCurveChart W i p ∈ integralSmoothOpen W := by
  let f : additionChartRing W i →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R _ _
  have hl := affineAlgebra_residue_nonsingular_at W (additionInputLeft W i) p hp.1
  have hr := affineAlgebra_residue_nonsingular_at W (additionInputRight W i) p hp.2
  have h := additionFieldPoint_chart_range_smooth W i f hl hr
  let z : Spec (.of p.asIdeal.ResidueField) := ⟨⊥, inferInstance⟩
  have hz : PrimeSpectrum.comap
      (algebraMap (additionChartRing W i) p.asIdeal.ResidueField) z = p :=
    Set.mem_singleton_iff.mp ((PrimeSpectrum.residueField_comap p) ▸ Set.mem_range_self z)
  have hm := h ⟨z, rfl⟩
  change additionCurveChart W i (PrimeSpectrum.comap
    (algebraMap (additionChartRing W i) p.asIdeal.ResidueField) z) ∈ _ at hm
  rwa [hz] at hm

/-- The original chart addition restricted to its actual smooth-input open. -/
def additionSmoothChart : (additionSmoothInputOpen W i).toScheme ⟶
    (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((additionSmoothInputOpen W i).ι ≫ additionCurveChart W i) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact additionSmoothInputOpen_output W i p.val p.property)

/-- The smooth chart retains the actual original formula in the glued cubic. -/
@[reassoc] theorem additionSmoothChart_inclusion :
    additionSmoothChart W i ≫ (integralSmoothOpen W).ι =
      (additionSmoothInputOpen W i).ι ≫ additionCurveChart W i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted chart is exactly the restriction of the original glued partial addition. -/
theorem additionSmoothChart_partial :
    additionSmoothChart W i ≫ (integralSmoothOpen W).ι =
      (additionSmoothInputOpen W i).ι ≫ additionChartToDomain W i ≫ affinePartialAddition W := by
  rw [additionChartToDomain_addition, additionSmoothChart_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
