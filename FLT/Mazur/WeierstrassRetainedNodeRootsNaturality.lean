/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeRoots
public import FLT.Mazur.NilpotentQuadraticRootNaturality

/-!
# Both full retained roots commute with the original coefficient maps

The target constructs its own roots in its own nilpotent ideal. Uniqueness
identifies them under the entire node-ring map, before either branch is inverted.
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
local notation "IR" => I.map (algebraMap R (ChartRing π))
local notation "JS" => J.map (algebraMap S (ChartRing (f π)))

include hf in
/-- The actual node coefficient map preserves the extended nilpotent ideals. -/
theorem retainedArithmeticIdeal_map : IR ≤ (JS).comap F := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change F (algebraMap R _ a) ∈ JS
  rw [ringMap_scalar]
  exact Ideal.mem_map_of_mem _ (hf ha)

/-- Coefficient substitution retains the entire regular linear term. -/
theorem retainedSlopeLinear_map :
    F (retainedSlopeLinear W π c3) = retainedSlopeLinear (W.map f) (f π) (f c3) := by
  unfold retainedSlopeLinear
  rw [RingHom.map_add, RingHom.map_mul, ringMap_scalar, ringMap_scalar, ringMap_left]
  rfl

/-- Coefficient substitution retains the complete regular conic constant. -/
theorem retainedConicConstant_map :
    F (retainedConicConstant W π c4 c6) =
      retainedConicConstant (W.map f) (f π) (f c4) (f c6) := by
  unfold retainedConicConstant
  rw [RingHom.map_add, RingHom.map_add, RingHom.map_mul, RingHom.map_mul,
    RingHom.map_pow,
    ringMap_scalar, ringMap_scalar,
    ringMap_scalar, ringMap_left]
  rfl

/-- The full smoothing term also follows the original coefficient map. -/
theorem retainedSlopeConstant_map :
    F (retainedSlopeConstant W π s c4 c6) =
      retainedSlopeConstant (W.map f) (f π) (f s) (f c4) (f c6) := by
  unfold retainedSlopeConstant
  rw [RingHom.map_add, RingHom.map_mul, ringMap_scalar, ringMap_right, retainedConicConstant_map]

variable (hI : IsNilpotent I) (hJ : IsNilpotent J) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)

/-- The independently constructed conic roots coincide under the full node-ring restriction. -/
theorem retainedConicRoot_map :
    F (retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6) =
      retainedConicRoot (W.map f) (f π) (f c3) (f c4) (f c6) J hJ (ha.map f)
        (hf h2) (hf h3) (hf h4) (hf h6) := by
  have h := NilpotentQuadraticRoot.root_map IR (retainedArithmeticIdeal_nilpotent π I hI)
    JS (retainedArithmeticIdeal_nilpotent (f π) J hJ)
    (retainedSlopeLinear W π c3) (retainedConicConstant W π c4 c6)
    (retainedSlopeLinear_unit W π c3 I hI ha h3)
    (retainedConicConstant_mem W π c4 c6 I h2 h4 h6) F
    (retainedArithmeticIdeal_map f π I J hf)
  simpa only [retainedConicRoot, retainedSlopeLinear_map, retainedConicConstant_map] using h

/-- Both entire smoothing-dependent roots agree under the same original node-ring map. -/
theorem retainedSlopeRoot_map :
    F (retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) =
      retainedSlopeRoot (W.map f) (f π) (f s) (f c3) (f c4) (f c6) J hJ (ha.map f)
        (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) := by
  have h := NilpotentQuadraticRoot.root_map IR (retainedArithmeticIdeal_nilpotent π I hI)
    JS (retainedArithmeticIdeal_nilpotent (f π) J hJ)
    (retainedSlopeLinear W π c3) (retainedSlopeConstant W π s c4 c6)
    (retainedSlopeLinear_unit W π c3 I hI ha h3)
    (retainedSlopeConstant_mem W π s c4 c6 I hs h2 h4 h6) F
    (retainedArithmeticIdeal_map f π I J hf)
  simpa only [retainedSlopeRoot, retainedSlopeLinear_map, retainedSlopeConstant_map] using h

end FLT.Mazur.WeierstrassModificationX
