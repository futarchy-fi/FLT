/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductCocycle
public import FLT.Mazur.SchemeOverlapCocycleChart

/-!
# The affine categorical cocycle as a scheme cocycle

Expose the actual pair and coordinate maps of the affine categorical cocycle
in the general scheme predicate, without specializing the coefficient sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineTripleOverlapMaps AffineOverlapTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) (e : FiberProductOverlap R S M)

/-- Pair transport exposes its normalization before the coordinate maps are specialized. -/
theorem fiberProductTransport_eq_normalize (t : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S) (hi : t.toRingHom.comp (left R S) = i)
    (hj : t.toRingHom.comp (right R S) = j) :
    fiberProductTransport R S M t i j hi hj e =
      SchemeOverlapDiagonalChart.normalize
        (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        (fiberProductPair R S t) (Spec.map (CommRingCat.ofHom i))
        (Spec.map (CommRingCat.ofHom j)) (fiberProductPair_fst R S t i hi)
        (fiberProductPair_snd R S t j hj) M e := rfl

/-- The categorical affine cocycle is exactly the general scheme cocycle on its pair maps. -/
theorem fiberProductCocycle_iff_scheme :
    FiberProductCocycle R S M e ↔ SchemeOverlapCocycleChart.CocycleCompatible
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (fiberProductPair R S (pair12 R S)) (fiberProductPair R S (pair23 R S))
      (fiberProductPair R S (pair13 R S))
      (Spec.map (CommRingCat.ofHom (coord1 R S)))
      (Spec.map (CommRingCat.ofHom (coord2 R S)))
      (Spec.map (CommRingCat.ofHom (coord3 R S)))
      (fiberProductPair_fst R S (pair12 R S) (coord1 R S) (pair12_left R S))
      (fiberProductPair_snd R S (pair12 R S) (coord2 R S) (pair12_right R S))
      (fiberProductPair_fst R S (pair23 R S) (coord2 R S) (pair23_left R S))
      (fiberProductPair_snd R S (pair23 R S) (coord3 R S) (pair23_right R S))
      (fiberProductPair_fst R S (pair13 R S) (coord1 R S) (pair13_left R S))
      (fiberProductPair_snd R S (pair13 R S) (coord3 R S) (pair13_right R S))
      M e := by
  unfold FiberProductCocycle SchemeOverlapCocycleChart.CocycleCompatible
  rw [fiberProductTransport_eq_normalize, fiberProductTransport_eq_normalize,
    fiberProductTransport_eq_normalize]

end FLT.Mazur.AffineGeometricOverlap
