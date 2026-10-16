/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeRootsNaturality
public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# Full retained correction units commute with coefficient change

Root uniqueness determines the entire opposite factor and its squared correction
on the original node, including its inverse.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
local notation "F" => (ringMap f π (f π) rfl : ChartRing π →+* ChartRing (f π))
variable (hI : IsNilpotent I) (hJ : IsNilpotent J) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "U" => retainedOppositeUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "U'" => retainedOppositeUnit (W.map f) (f π) (f s) (f c3) (f c4)
  (f c6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "V" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "V'" => retainedFactorCorrectionUnit (W.map f) (f π) (f s) (f c3) (f c4)
  (f c6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

/-- The complete opposite factor follows the original node coefficient map. -/
theorem retainedOppositeFactor_map :
    F (retainedOppositeFactor W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) =
      retainedOppositeFactor (W.map f) (f π) (f s) (f c3) (f c4) (f c6) J hJ
        (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) := by
  unfold retainedOppositeFactor
  rw [RingHom.map_add, RingHom.map_add, retainedSlopeRoot_map f W π s c3 c4 c6 I J hf,
    retainedConicRoot_map f W π c3 c4 c6 I J hf, retainedSlopeLinear_map]

/-- The constructed whole-node unit agrees with the independently constructed target unit. -/
theorem retainedOppositeUnit_map : Units.map (F).toMonoidHom U = U' := by
  apply Units.ext
  change F (U : ChartRing π) = (U' : ChartRing (f π))
  rw [retainedOppositeUnit_val, retainedOppositeUnit_val,
    retainedOppositeFactor_map f W π s c3 c4 c6 I J hf]

/-- The entire squared correction is preserved, including its tangent normalization. -/
theorem retainedFactorCorrectionUnit_map : Units.map (F).toMonoidHom V = V' := by
  unfold retainedFactorCorrectionUnit
  rw [map_mul, map_pow, map_pow, map_inv,
    retainedOppositeUnit_map f W π s c3 c4 c6 I J hf hI hJ ha hs h2 h3 h4 h6]
  congr 2
  apply Units.ext
  change F (algebraMap R _ (zeroInitialTangentUnit W ha : R)) =
    algebraMap S _ (zeroInitialTangentUnit (W.map f) (ha.map f) : S)
  rw [ringMap_scalar]
  rfl

end FLT.Mazur.WeierstrassModificationX
