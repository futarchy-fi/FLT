/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStages
public import FLT.Mazur.WeierstrassCoefficientChartTransport

/-!
# The original Y charts under adjacent adic reduction

The explicit coefficient ring map is precisely the restriction of the actual
smooth-group coefficient comparison. This lets the constructed group tower
retain its original chart coordinates, rather than choosing unrelated affine
models at successive stages.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDividedDepth
open AdicFormallySmoothStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) (t : R) (ht : t ∈ I) (m : ℕ)

/-- The original Y chart is the entire smooth group at each nilpotent stage. -/
def stageChartIso : chartScheme (equation (parameter I t m)) 1 ≅ (stageGroup I t m).X.left :=
  nilpotentSmoothChartIso (parameter I t m) (parameter_nilpotent I t ht m)

/-- The chart identification retains the original cubic inclusion. -/
@[reassoc] theorem stageChartIso_hom_inclusion :
    (stageChartIso I t ht m).hom ≫ (integralSmoothOpen (equation (parameter I t m))).ι =
      integralCurveChart (equation (parameter I t m)) 1 := by
  unfold stageChartIso nilpotentSmoothChartIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac ..

/-- The full coordinate ring map between adjacent original Y charts. -/
def chartRestrictionRingMap : Coordinate (equation (parameter I t (m + 1))) 1 →+*
    Coordinate (equation (parameter I t m)) 1 :=
  chartCoefficientRingMapTo (restriction I m).toRingHom
    (equation (parameter I t (m + 1))) 1 (equation (parameter I t m))
    (restriction_equation I t m)

/-- The actual adjacent map of original Y charts. -/
def chartRestriction : chartScheme (equation (parameter I t m)) 1 ⟶
    chartScheme (equation (parameter I t (m + 1))) 1 :=
  Spec.map (CommRingCat.ofHom (chartRestrictionRingMap I t m))

/-- Chart restriction is the actual smooth-group comparison in the proved affine charts. -/
theorem chartRestriction_smooth :
    chartRestriction I t m ≫ (stageChartIso I t ht (m + 1)).hom =
      (stageChartIso I t ht m).hom ≫ smoothRestriction I t m := by
  let _ := (restriction I m).toRingHom.toAlgebra
  apply (cancel_mono (integralSmoothOpen (equation (parameter I t (m + 1)))).ι).mp
  rw [Category.assoc, stageChartIso_hom_inclusion]
  simp only [smoothRestriction, Category.assoc, originalSmoothCoefficientMap_inclusion,
    RingHom.algebraMap_toAlgebra]
  rw [equationTransport_smoothInclusion_assoc (restriction_equation I t m).symm,
    stageChartIso_hom_inclusion_assoc]
  exact chartCoefficientRingMapTo_inclusion (restriction I m).toRingHom
    (equation (parameter I t (m + 1))) 1 (equation (parameter I t m))
    (restriction_equation I t m)

end FLT.Mazur.OneGonAdicCharacterTower
