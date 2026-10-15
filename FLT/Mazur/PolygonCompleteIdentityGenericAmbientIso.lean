/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGenericAmbientKernel
public import FLT.Mazur.PowerSeriesFractionGenericOpen

/-!
# The original generic ambient relation is the original generic smooth graph

The inverse uses the constructed original smooth source and the same generic
coefficient map. Both directions retain the original ambient inclusion.
This is an isomorphism of the full generic schemes, before any adic reduction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "v" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "s" => completeIdentityActionLiftSpaceStructure K n h
local notation "r" => completeIdentityActionGenericAmbientInclusion K n h
local notation "l" => completeIdentityActionGenericAmbientToSmooth K n h
local notation "j" => completeIdentityGenericSmoothToAmbient K n h
local notation "b" => Spec.map
  (CommRingCat.ofHom (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))

/-- The actual smooth source together with the original generic coefficient coordinate. -/
def completeIdentityGenericAmbientToSmoothFiber :
    completeIdentityActionGenericAmbient K n h ⟶
      completeIdentityActionGenericSmoothInput K n h :=
  pullback.lift (l) (pullback.snd (s) (b)) (by
    rw [completeIdentityActionGenericAmbientToSmooth_inclusion_assoc]
    exact pullback.condition)
local notation "w" => completeIdentityGenericAmbientToSmoothFiber K n h

/-- The inverse factorization has the original ambient map, with no change of coordinates. -/
@[reassoc] theorem completeIdentityGenericAmbientToSmoothFiber_graph : (w) ≫ (g) = (r) := by
  rw [completeIdentityActionGenericSmoothGraph, ← Category.assoc,
    completeIdentityGenericAmbientToSmoothFiber, pullback.lift_fst,
    completeIdentityActionGenericAmbientToSmooth_graph]

/-- The generic graph is a monomorphism, so its actual coordinates detect the inverse identity. -/
instance completeIdentityActionGenericSmoothGraph_mono : Mono (g) := by
  unfold completeIdentityActionGenericSmoothGraph
  infer_instance

/-- The whole generic ambient relation equals the original generic smooth graph as a scheme. -/
def completeIdentityGenericAmbientIso :
    completeIdentityActionGenericSmoothInput K n h ≅
      completeIdentityActionGenericAmbient K n h where
  hom := (j)
  inv := (w)
  hom_inv_id := (cancel_mono (g)).mp (by
    rw [Category.assoc, completeIdentityGenericAmbientToSmoothFiber_graph,
      completeIdentityGenericSmoothToAmbient_inclusion, Category.id_comp])
  inv_hom_id := (cancel_mono (r)).mp (by
    rw [Category.assoc, completeIdentityGenericSmoothToAmbient_inclusion,
      completeIdentityGenericAmbientToSmoothFiber_graph, Category.id_comp])

/-- The constructed generic isomorphism respects the exact original complete ambient inclusion. -/
@[reassoc] theorem completeIdentityGenericAmbientIso_inclusion :
    (completeIdentityGenericAmbientIso K n h).hom ≫ (r) = (g) :=
  completeIdentityGenericSmoothToAmbient_inclusion K n h

end FLT.Mazur.PolygonInfinitesimalStages
