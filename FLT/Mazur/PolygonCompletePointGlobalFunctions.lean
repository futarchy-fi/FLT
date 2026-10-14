/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicChartFunctions
public import FLT.Mazur.PolygonCompletePointIdentityOpenMarking
public import FLT.Mazur.CartesianOpenFunctionSheaf
public import FLT.Mazur.WeierstrassOriginComplement

/-!
# The global original contraction preserves the structure sheaf

Glue the actual affinization on the Z chart to the unchanged identity
neighborhood. No smooth-group hypothesis is imposed on the original polygon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointIdentityCubicOpen

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "Z" => Scheme.Hom.opensRange (integralCurveChart (W) 2)
local notation "T" => completePointIdentityCubicOpen K n h i

/-- The actual identity neighborhood and Z chart cover the original integral cubic. -/
theorem completePointCubic_function_cover : (T) ⊔ (Z) = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ (Z)
  · exact Or.inr hx
  · exact Or.inl (completePointIdentityCubicOpen_zero_range K n h i
      ((integralCurve_notMem_affine_iff (W) x).mp hx))

/-- The original structure-sheaf map is an isomorphism on the whole integral cubic. -/
theorem completePointToIntegralCubic_structureMap_isIso :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := g)) := by
  let C : Bool → (integralCurve (W)).Opens := fun j ↦ if j then (T) else (Z)
  apply CartesianOpenFunctionSheaf.structureMap_isIso_of_cover (g) C
  · intro x
    have hx : x ∈ (T) ⊔ (Z) := by rw [completePointCubic_function_cover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro j V hV
    cases j with
    | false =>
      exact CartesianOpenFunctionSheaf.app_isIso_of_chart (g)
        (completePointComplementToCubicChart K n h i) _ (integralCurveChart (W) 2)
        (completePointComplementToCubicChart_isPullback K n h i)
        (completePointComplementToCubicChart_app_isIso K n h i) V hV
    | true =>
      let _ := completePointIdentityCubicOpen_isIso K n h i
      exact CartesianOpenFunctionSheaf.app_isIso_of_restriction (g) (T) V hV
        (fun _ ↦ inferInstance)

/-- The global direct-image ring sheaf, with the original contraction as forward map. -/
def completePointCubicStructureSheafIso :
    (integralCurve (W)).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat (g).base).obj
        (exactVeroneseProj K n h).sheaf := by
  let _ := completePointToIntegralCubic_structureMap_isIso K n h i
  exact asIso (ArtinianProperStructureSheaf.structureMap (q := g))

/-- The global identification retains the actual function pullback on every open. -/
theorem completePointCubicStructureSheafIso_app (V : (integralCurve (W)).Opens) :
    (completePointCubicStructureSheafIso K n h i).hom.hom.app (.op V) = (g).app V :=
  rfl

/-- Functions on any inverse-image open come uniquely from the original cubic open. -/
theorem completePointToIntegralCubic_app_isIso (V : (integralCurve (W)).Opens) :
    IsIso ((g).app V) := by
  let _ := completePointToIntegralCubic_structureMap_isIso K n h i
  exact inferInstanceAs
    (IsIso ((completePointCubicStructureSheafIso K n h i).hom.hom.app (.op V)))

end FLT.Mazur.PolygonInfinitesimalStages
