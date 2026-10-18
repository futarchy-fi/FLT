/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSquareZeroTorsionRigidity
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Square-zero parameters in the full smooth group

Every infinitesimal identity-chart parameter lands in the smooth locus, even
when the discriminant is not a unit. Its reduction and its original chart
coordinates are retained as scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- Reduction of a square-zero chart parameter is the original infinity section. -/
theorem infinitesimalChartPoint_spec_reduction (x : I) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
        integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I))) ≫ integralCurveZero W := by
  have he := (infinitesimalChart_iff_reduction W I
    (infinitesimalChartPoint W I hI x).val).mp (infinitesimalChartPoint W I hI x).property
  have hs := congrArg (fun f : Coordinate W 1 →ₐ[R] A ⧸ I ↦
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 1) he
  rw [chartInfinityEvaluation_base (S := A ⧸ I)] at hs
  change Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk I).comp (infinitesimalChartPoint W I hI x).val.toRingHom)) ≫ _ = _ at hs
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    integralCurveZero] using hs

/-- Square-zero parameters lie in the smooth locus over every coefficient ring. -/
theorem infinitesimalChartPoint_range_smooth (x : I) :
    Set.range (Spec.map
      (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
        integralCurveChart W 1) ⊆ integralSmoothOpen W := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ := squareZero_quotient_spec_surjective I hI a
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ _ ≫ _) b ∈ _
  rw [infinitesimalChartPoint_spec_reduction]
  exact integralCurveZero_range_smooth W ⟨_, rfl⟩

/-- The actual smooth-group point with the prescribed infinitesimal X coordinate. -/
def smoothInfinitesimalPoint (x : I) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X :=
  Over.homMk (IsOpenImmersion.lift (integralSmoothOpen W).ι
    (Spec.map (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
      integralCurveChart W 1) (by
        exact (infinitesimalChartPoint_range_smooth W I hI x).trans_eq
          (Scheme.Opens.range_ι _).symm)) (by
    change _ ≫ (integralSmoothOpen W).ι ≫ integralCurveStructure W = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
      integralCurveChart_structure, chartStructure, specAlgHom_structure]
    rfl)

/-- Passing to the original curve recovers the full original infinitesimal chart map. -/
@[reassoc] theorem smoothInfinitesimalPoint_inclusion (x : I) :
    (smoothInfinitesimalPoint W I hI x).left ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
        integralCurveChart W 1 := IsOpenImmersion.lift_fac _ _ _

omit I hI in
/-- The identity of the full smooth group is the original infinity section. -/
theorem smoothGroupPoint_one_inclusion :
    (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X).left ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := A) W).toRingHom) ≫
        integralCurveChart W 1 := by
  change (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ integralSmoothZero W) ≫ _ = _
  rw [Category.assoc, integralSmoothZero_inclusion, integralCurveZero,
    ← Category.assoc, ← Spec.map_comp, chartInfinityEvaluation_base (S := A)]
  rfl

/-- Every constructed parameter belongs to the actual square-zero reduction kernel. -/
theorem smoothInfinitesimalPoint_reduction (x : I) :
    squareZeroQuotientTestMap I ≫ smoothInfinitesimalPoint W I hI x = 1 := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ _) ≫ _ = _
  rw [Category.assoc, smoothInfinitesimalPoint_inclusion,
    infinitesimalChartPoint_spec_reduction, smoothGroupPoint_one_inclusion,
    integralCurveZero, ← Category.assoc, ← Spec.map_comp,
    chartInfinityEvaluation_base (S := A ⧸ I)]
  rfl

/-- The original X coordinate distinguishes these actual smooth-group points. -/
theorem smoothInfinitesimalPoint_injective :
    Function.Injective (smoothInfinitesimalPoint W I hI) := by
  intro x y h
  have he := congrArg (fun p ↦ p.left ≫ (integralSmoothOpen W).ι) h
  rw [smoothInfinitesimalPoint_inclusion, smoothInfinitesimalPoint_inclusion] at he
  have he' := Spec.map_injective ((cancel_mono (integralCurveChart W 1)).mp he)
  apply Subtype.ext
  have hc := congrArg (fun g : CommRingCat.of (Coordinate W 1) ⟶ CommRingCat.of A ↦
    g.hom (coord W 1 0)) he'
  change (infinitesimalChartPoint W I hI x).val (coord W 1 0) =
    (infinitesimalChartPoint W I hI y).val (coord W 1 0) at hc
  simpa only [infinitesimalChartPoint_x] using hc

end FLT.Mazur.WeierstrassIntegralChart
