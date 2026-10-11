/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleVeroneseIso
public import FLT.Mazur.GradedDegreeProjStructuralMap

/-!
# Common-step comparison over the original complete base

The inclusion preserves the actual power-series scalar action, so both
maps of the global comparison preserve the original structural morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q r : ℕ) [NeZero q]

/-- Common-degree inclusion retains the actual complete coefficient action. -/
theorem multipleVeroneseInclusion_algebraMap (a : PowerSeries R) :
    multipleVeroneseInclusion R n h q r
        (algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h (q * r)) a) =
      algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h q) a := by
  apply compatibleVeroneseToSections_injective R n h q (NeZero.pos q)
  change compatibleVeroneseToSections R n h q
    (multipleVeroneseAddInclusion R n h q r
      (algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h (q * r)) a)) = _
  rw [multipleVeroneseAddInclusion_recompose]
  change DirectSum.coeAlgHom (compatibleVeroneseDegree R n h (q * r))
    (algebraMap (PowerSeries R) _ a) =
      DirectSum.coeAlgHom (compatibleVeroneseDegree R n h q) (algebraMap (PowerSeries R) _ a)
  rw [AlgHom.commutes, AlgHom.commutes]

/-- The scalar structural morphism at any retained step. -/
def multipleVeroneseToBase :
    Proj (compatibleVeroneseGrade R n h q) ⟶ Spec (.of (PowerSeries R)) :=
  GradedProjStructuralMap.toSpecBase (compatibleVeroneseGrade R n h q)

/-- The global forward comparison is over the original power-series base. -/
@[reassoc]
theorem multipleVeroneseProjIso_hom_toBase (hr : 0 < r) :
    (multipleVeroneseProjIso R n h q r hr).hom ≫ multipleVeroneseToBase R n h (q * r) =
      multipleVeroneseToBase R n h q :=
  GradedDegreeProjStructuralMap.map_toSpecBase _ _ _ _
    (multipleVeroneseInclusion_mem R n h q r)
    (multipleVeroneseInclusion_algebraMap R n h q r) hr
    (multipleVeronese_common_charts_cover R n h q r hr)

/-- The inverse comparison is over the same original complete base. -/
@[reassoc]
theorem multipleVeroneseProjIso_inv_toBase (hr : 0 < r) :
    (multipleVeroneseProjIso R n h q r hr).inv ≫ multipleVeroneseToBase R n h q =
      multipleVeroneseToBase R n h (q * r) := by
  rw [Iso.inv_comp_eq, multipleVeroneseProjIso_hom_toBase]

end FLT.Mazur.PolygonInfinitesimalStages
