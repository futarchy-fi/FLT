/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginIdealEquality
public import FLT.Mazur.CartierPullbackParameterRegular

/-!
# The original identity parameter stays regular under the cubic morphism

The full marking-ideal comparison proves cancellation for the actual pulled
parameter, on the entire parameter preimage and every original open chart.
No flatness of the cubic morphism or affineness of its preimage is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i

/-- The pulled neighborhood origin ideal is Cartier on the original parameter preimage. -/
theorem completePointOriginPulledParameter_cartier :
    EffectiveCartier ((originNeighborhoodSection (W)).ker.comap (q)) := by
  rw [← completePointPulledOriginIdeal_neighborhood,
    completePointPulledOriginIdeal_eq_marking]
  exact (completePointFirstOrderCartier K n h i).comap_of_isOpenImmersion (V).ι

/-- The actual pulled parameter cancels in the entire original neighborhood section ring. -/
theorem completePointToOrigin_parameter_regular :
    IsRegular ((q).appTop (originParameterSection (W))) :=
  cartierPullbackParameter_regular (q) (originNeighborhoodSection (W)).ker
    (originParameterSection (W)) (originIdealSheaf_section_equation (W))
    (completePointOriginPulledParameter_cartier K n h i)

/-- Cancellation retains the actual structure maps on every original open subscheme. -/
theorem completePointToOrigin_parameter_regular_on (U : (V).toScheme.Opens) :
    IsRegular ((U.ι ≫ (q)).appTop (originParameterSection (W))) := by
  apply cartierPullbackParameter_regular (U.ι ≫ (q)) (originNeighborhoodSection (W)).ker
    (originParameterSection (W)) (originIdealSheaf_section_equation (W))
  rw [Scheme.IdealSheafData.comap_comp]
  exact (completePointOriginPulledParameter_cartier K n h i).comap_of_isOpenImmersion U.ι

/-- The regularity comparison also holds in each original neighborhood local ring. -/
theorem completePointToOrigin_parameter_germ_regular (x : (V).toScheme) :
    IsRegular ((V).toScheme.presheaf.Γgerm x ((q).appTop (originParameterSection (W)))) :=
  cartierPullbackParameter_germ_regular (q) (originNeighborhoodSection (W)).ker
    (originParameterSection (W)) (originIdealSheaf_section_equation (W))
    (completePointOriginPulledParameter_cartier K n h i) x

end FLT.Mazur.PolygonInfinitesimalStages
