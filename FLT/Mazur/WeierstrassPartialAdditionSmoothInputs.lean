/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineRelativeSmoothCriterion
public import FLT.Mazur.WeierstrassPartialAdditionSmoothResidues

/-!
# Partial addition preserves actual smooth inputs over arbitrary rings

The geometric input condition now supplies the residue-field nonsingularity
test. Every original chart therefore has an actual output in the relative
smooth locus for every coefficient equation and every affine source scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Smooth affine-chart inputs stay nonsingular after passing to any source residue field. -/
theorem affineAlgebra_residue_nonsingular (f : Coordinate W 2 →ₐ[R] S)
    (hs : Set.range (Spec.map (CommRingCat.ofHom f.toRingHom)) ⊆
      (chartStructure W 2).smoothLocus) (p : PrimeSpectrum S) :
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
  exact hs ⟨(Spec.map (CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField))) z, rfl⟩

variable (i : AdditionChartIndex) (f : additionChartRing W i →ₐ[R] S)
  (hl : Set.range (Spec.map (CommRingCat.ofHom
      (f.comp (additionInputLeft W i)).toRingHom)) ⊆ (chartStructure W 2).smoothLocus)
  (hr : Set.range (Spec.map (CommRingCat.ofHom
      (f.comp (additionInputRight W i)).toRingHom)) ⊆ (chartStructure W 2).smoothLocus)

include hl hr

/-- All four original addition formulas preserve actual relative smoothness of the inputs. -/
theorem additionAlgebra_chart_range_smooth_of_inputs :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i) ⊆
      integralSmoothOpen W := by
  apply additionAlgebra_chart_range_smooth
  intro p
  exact ⟨affineAlgebra_residue_nonsingular W (f.comp (additionInputLeft W i)) hl p,
    affineAlgebra_residue_nonsingular W (f.comp (additionInputRight W i)) hr p⟩

/-- The actual chart output as a morphism into the relative smooth locus. -/
def additionSmoothInputOutput : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i)
    (by rw [Scheme.Opens.range_ι]; exact additionAlgebra_chart_range_smooth_of_inputs W i f hl hr)

/-- The smooth output retains the original chart morphism exactly. -/
@[reassoc] theorem additionSmoothInputOutput_inclusion :
    additionSmoothInputOutput W i f hl hr ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth output is also the value of the original glued partial addition. -/
theorem additionSmoothInputOutput_partial :
    additionSmoothInputOutput W i f hl hr ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain W i ≫ affinePartialAddition W := by
  rw [additionChartToDomain_addition, additionSmoothInputOutput_inclusion]

/-- The smooth output preserves the original coefficient map. -/
theorem additionSmoothInputOutput_structure :
    additionSmoothInputOutput W i f hl hr ≫ integralSmoothStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [integralSmoothStructure, ← Category.assoc, additionSmoothInputOutput_inclusion,
    Category.assoc, additionCurveChart_structure, additionChartInclusion.eq_def,
    ← additionChartAlgRestriction_toRingHom,
    specAlgHom_structure (additionChartAlgRestriction W i)]
  exact specAlgHom_structure f

end FLT.Mazur.WeierstrassIntegralChart
