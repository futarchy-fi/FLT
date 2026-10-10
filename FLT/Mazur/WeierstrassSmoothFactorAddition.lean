/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionGluing
public import FLT.Mazur.WeierstrassSmoothFactorProduct

/-!
# Addition on the categorical smooth-factor product

Transporting the glued law along the explicit product isomorphism gives an
actual morphism over the coefficient base. Its restrictions are the original
smooth chart laws, for every equation and every reduction type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Each original smooth tensor chart maps into the full smooth product open. -/
def smoothProductChartToOpen (b c : Bool) :
    (smoothProductChartOpen W b c).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  IsOpenImmersion.lift (smoothCurveProductOpen W).ι (smoothProductChartInput W b c) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact p.property)

/-- The smooth chart map preserves its original global input pair. -/
@[reassoc] theorem smoothProductChartToOpen_inclusion (b c : Bool) :
    smoothProductChartToOpen W b c ≫ (smoothCurveProductOpen W).ι =
      smoothProductChartInput W b c := IsOpenImmersion.lift_fac _ _ _

/-- The global smooth law restricts to the original law on every full smooth input chart. -/
@[reassoc] theorem smoothProductChartToOpen_addition (b c : Bool) :
    smoothProductChartToOpen W b c ≫ smoothCurveAddition W = smoothInputAddition W b c := by
  simpa only [Category.id_comp] using smoothCurveAddition_commonScheme W b c
    (smoothProductChartToOpen W b c) (𝟙 _)
    (by rw [smoothProductChartToOpen_inclusion, Category.id_comp])

/-- The coefficient morphism of each smooth chart agrees with its global input morphism. -/
theorem smoothInputAddition_structure_global (b c : Bool) :
    smoothInputAddition W b c ≫ integralSmoothStructure W =
      smoothProductChartInput W b c ≫
        pullback.fst (integralCurveStructure W) (integralCurveStructure W) ≫
          integralCurveStructure W := by
  rw [smoothInputAddition_structure, smoothProductChartInput,
    Category.assoc, ← Category.assoc (integralCurveProductChart W b c),
    integralCurveProductChart_fst, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure (chartProductLeft W
      (productChartCoordinate b) (productChartCoordinate c))]

/-- The glued smooth addition is over the original coefficient scheme. -/
theorem smoothCurveAddition_structure :
    smoothCurveAddition W ≫ integralSmoothStructure W =
      smoothProductFst W ≫ integralSmoothStructure W := by
  apply (smoothCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  rw [← Category.assoc, smoothCurveProductCover_addition, Category.assoc,
    smoothInputAddition_structure_global, ← Category.assoc,
    smoothCurveProductCoverToChart_inputs, Category.assoc]
  rw [integralSmoothStructure, smoothProductFst_inclusion_assoc]

/-- Addition on the actual categorical product of the relative smooth curves. -/
def smoothFactorAddition : smoothFactorProduct W ⟶ (integralSmoothOpen W).toScheme :=
  smoothFactorsToProduct W ≫ smoothCurveAddition W

/-- The categorical smooth addition is a morphism over the coefficient base. -/
theorem smoothFactorAddition_structure :
    smoothFactorAddition W ≫ integralSmoothStructure W =
      pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) ≫
        integralSmoothStructure W := by
  have hf : smoothFactorsToProduct W ≫ smoothProductFst W =
      pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) := by
    apply (cancel_mono (integralSmoothOpen W).ι).mp
    rw [Category.assoc, smoothProductFst_inclusion, ← Category.assoc,
      smoothFactorsToProduct_inclusion, smoothFactorsInclusion, pullback.lift_fst]
  rw [smoothFactorAddition, Category.assoc, smoothCurveAddition_structure,
    ← Category.assoc, hf]

/-- Returning to the smooth product open recovers the original glued addition. -/
@[reassoc] theorem smoothProductToFactors_addition :
    smoothProductToFactors W ≫ smoothFactorAddition W = smoothCurveAddition W := by
  rw [smoothFactorAddition, ← Category.assoc]
  have hi : smoothProductToFactors W ≫ smoothFactorsToProduct W = 𝟙 _ :=
    (smoothProductFactorsIso W).hom_inv_id
  rw [hi, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart
