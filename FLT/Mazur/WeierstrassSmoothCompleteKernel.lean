/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothCompleteRoots
public import FLT.Mazur.PowerSeriesSmoothPointLift

/-!
# Complete kernel powers for the original coefficient surjection

The quotient-kernel comparison transfers complete root reconstruction to an
arbitrary surjective coefficient map, retaining the original target ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.WeierstrassSmoothCompleteKernel

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open WeierstrassIntegralChart WeierstrassSmoothAdicReduction
variable {R B : Type} [CommRing R] [CommRing B]
  [Algebra R B] (W : WeierstrassCurve R) (φ : R →ₐ[R] B)
  (hφ : Function.Surjective φ)

include hφ in
/-- The original coefficient map has precisely the first adic-reduction kernel. -/
theorem reduction_kernel : (smoothAlgebraReduction W φ).ker =
    (sectionReduction W (RingHom.ker φ.toRingHom) 0).ker := by
  rw [smoothAlgebraReduction_ker W φ hφ]
  change (smoothSquareZeroReduction W (RingHom.ker φ.toRingHom)).ker =
    (smoothSquareZeroReduction W ((RingHom.ker φ.toRingHom) ^ (0 + 1))).ker
  rw [pow_one]

variable [IsLocalRing R] [Nontrivial B] [IsAdicComplete (RingHom.ker φ.toRingHom) R]

include hφ in
/-- Completeness and a unit index make powers bijective on the entire original kernel. -/
theorem kernel_pow_bijective (n : ℕ) (hn : IsUnit (n : R)) :
    Function.Bijective (fun z : (smoothAlgebraReduction W φ).ker ↦ z ^ n) := by
  rw [reduction_kernel W φ hφ]
  exact WeierstrassSmoothCompleteRoots.kernel_pow_bijective W (RingHom.ker φ.toRingHom)
    (RingHom.ker_ne_top φ.toRingHom) n hn

end FLT.Mazur.WeierstrassSmoothCompleteKernel
