/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassClosureSmoothGroupOperations
public import FLT.Mazur.CartesianMonoGroup

/-!
# The actual smooth kernel intersection is a commutative group scheme

All group laws follow by cancellation against the original closed inclusion.
The carrier is the same smooth intersection of the same finite flat closure;
no finiteness or singular-locus avoidance is asserted for this open part.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  (G : CommGrp (Over (Spec (.of K)))) (f : G ⟶ integralCurveGroup _ hΔ)
  [IsClosedImmersion f.hom.hom.hom.left]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))]

local notation "i" => f.hom.hom.hom.left
local notation "s" => genericClosureSmoothStructure W i
local notation "j" => genericClosureSmoothOverInclusion W i

/-- The actual smooth kernel intersection has the constructed commutative group laws. -/
@[instance_reducible] def genericClosureSmoothCommGrpObj : CommGrpObj (Over.mk s) := by
  let _ := integralSmoothCommGrpObj W
  exact CartesianMonoGroup.commGrpObj j (genericClosureSmoothOverZero W hΔ G f)
    (genericClosureSmoothOverMultiplication W hΔ G f) (genericClosureSmoothOverNegation W hΔ G f)
    (genericClosureSmoothOverZero_inclusion W hΔ G f)
    (genericClosureSmoothOverMultiplication_inclusion W hΔ G f)
    (genericClosureSmoothOverNegation_inclusion W hΔ G f)

/-- Bundle the retained smooth intersection with its original coefficient morphism. -/
def genericClosureSmoothGroup : CommGrp (Over (Spec (.of R))) := by
  let _ := genericClosureSmoothCommGrpObj W hΔ G f
  exact ⟨Over.mk s⟩

/-- The carrier remains the exact original smooth intersection over its original base. -/
theorem genericClosureSmoothGroup_carrier :
    (genericClosureSmoothGroup W hΔ G f).X = Over.mk s := rfl

/-- The original closed inclusion preserves the constructed integral group operations. -/
theorem genericClosureSmoothGroup_inclusion_isMonHom :
    let _ := genericClosureSmoothCommGrpObj W hΔ G f
    let _ := integralSmoothCommGrpObj W
    IsMonHom j := by
  let _ := genericClosureSmoothCommGrpObj W hΔ G f
  let _ := integralSmoothCommGrpObj W
  exact ⟨genericClosureSmoothOverZero_inclusion W hΔ G f,
    genericClosureSmoothOverMultiplication_inclusion W hΔ G f⟩

/-- The exact original closed inclusion as a morphism of commutative group schemes. -/
def genericClosureSmoothGroupInclusion :
    genericClosureSmoothGroup W hΔ G f ⟶ integralSmoothGroup W := by
  let _ := genericClosureSmoothGroup_inclusion_isMonHom W hΔ G f
  exact ⟨Grp.ofHom j⟩

/-- The bundled group inclusion is precisely the original smooth intersection inclusion. -/
theorem genericClosureSmoothGroupInclusion_left :
    (genericClosureSmoothGroupInclusion W hΔ G f).hom.hom.hom.left =
      genericClosureSmoothInclusion W i := rfl

end FLT.Mazur.WeierstrassIntegralChart
