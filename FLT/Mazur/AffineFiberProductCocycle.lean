/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductPairTransport
public import FLT.Mazur.AffinePullbackNormalization
public import FLT.Mazur.AffineTripleOverlapPullback
public import FLT.Mazur.SchemeOverlapTransportComposition

/-!
# The cocycle law on categorical double overlaps

Normalize the categorical double-overlap isomorphism along the three maps
from the affine triple overlap. Its cocycle is equivalent to the existing
affine tensor-chart cocycle, using composition coherence of sheaf pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

variable (M : (Spec (.of S)).Modules)

/-- Express affine pair transport using the general scheme comparison. -/
theorem transport_eq_normalize (t : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S) (hi : t.toRingHom.comp (left R S) = i)
    (hj : t.toRingHom.comp (right R S) = j) (e : Overlap R S M) :
    transport R S M t i j hi hj e = normalize
      (Spec.map (CommRingCat.ofHom (left R S))) (Spec.map (CommRingCat.ofHom (right R S)))
      (Spec.map (CommRingCat.ofHom t.toRingHom))
      (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom j))
      (spec_comp (left R S) t.toRingHom i hi)
      (spec_comp (right R S) t.toRingHom j hj) M e := by
  exact AffineIteratedPullbackSections.compositeIso_normalize _ _ _ _ _ _ _ M e

/-- The tensor-chart pair transport equals direct transport of the categorical overlap. -/
theorem fromFiberProduct_transport (t : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S) (hi : t.toRingHom.comp (left R S) = i)
    (hj : t.toRingHom.comp (right R S) = j) (e : FiberProductOverlap R S M) :
    transport R S M t i j hi hj (fromFiberProduct R S M e) =
      fiberProductTransport R S M t i j hi hj e := by
  rw [transport_eq_normalize, fromFiberProduct_eq_normalize]
  exact normalize_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ M e

/-- The categorical overlap cocycle, tested on the actual affine triple-overlap scheme. -/
def FiberProductCocycle (e : FiberProductOverlap R S M) : Prop :=
  (fiberProductTransport R S M (pair12 R S) (coord1 R S) (coord2 R S)
      (pair12_left R S) (pair12_right R S) e).hom ≫
    (fiberProductTransport R S M (pair23 R S) (coord2 R S) (coord3 R S)
      (pair23_left R S) (pair23_right R S) e).hom =
    (fiberProductTransport R S M (pair13 R S) (coord1 R S) (coord3 R S)
      (pair13_left R S) (pair13_right R S) e).hom

/-- Tensor-chart normalization preserves and detects the actual geometric cocycle. -/
theorem fromFiberProduct_cocycle_iff (e : FiberProductOverlap R S M) :
    CocycleCompatible R S M (fromFiberProduct R S M e) ↔ FiberProductCocycle R S M e := by
  unfold CocycleCompatible transport12 transport23 transport13 FiberProductCocycle
  rw [fromFiberProduct_transport, fromFiberProduct_transport, fromFiberProduct_transport]

/-- The categorical overlap reconstructed from an affine datum has its supplied cocycle. -/
theorem toFiberProduct_cocycle (e : Overlap R S M) (he : CocycleCompatible R S M e) :
    FiberProductCocycle R S M (toFiberProduct R S M e) := by
  apply (fromFiberProduct_cocycle_iff R S M _).mp
  simpa only [fromFiberProduct_toFiberProduct] using he

end FLT.Mazur.AffineGeometricOverlap
