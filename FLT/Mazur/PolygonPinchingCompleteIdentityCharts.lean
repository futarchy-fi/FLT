/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPinchingCompleteClosedComparison
public import FLT.Mazur.PolygonCompleteClosedChartComparison
import all FLT.Mazur.PolygonPinchingCompleteClosedComparison

/-!
# Original identity charts inside the full pinching comparison

The map that includes all singular nodes restricts on each original
normalization torus to the complete family's original translated identity
chart. Thus its finite label is retained before any further arithmetic
change of Laurent coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
  completeClosedPolygon_lfp
variable (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (hp : IsPushout (toComponents K n (by omega)) (toNodes K n) p q)
local notation "e" => pinchingCompleteClosedIso K n hn p q hp
local notation "π" => exactVeroneseProjToBase K n hn

/-- Each original normalization torus is the correspondingly labeled complete identity chart. -/
@[reassoc] theorem pinchingCompleteClosedIso_identityChart (i : Fin n) :
    (torusToComponent K ≫ componentι K n i ≫ p).left ≫
        (e).hom ≫ pullback.fst _ _ =
      completePointIdentityClosedTorus K n hn (0 : Fin n) ≫
        (completeIdentityChart K n hn 0 (ZMod.finEquiv n i)).left ≫ (π).smoothLocus.ι := by
  change (torusToComponent K).left ≫ (componentι K n i ≫ p).left ≫ _ ≫ _ = _
  rw [pinchingCompleteClosedIso_component]
  have H := congrArg (fun f => f ≫ (π).smoothLocus.ι)
    (completeClosedFiniteChart_zeroIdentityChart K n hn i)
  rw [Category.assoc, completeClosedSmoothInclusion_inclusion,
    completeClosedFiniteChart_inclusion_assoc] at H
  simpa only [Over.comp_left, Category.assoc] using H

end FLT.Mazur.PolygonInfinitesimalStages
