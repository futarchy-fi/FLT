/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductCocycleChart
public import FLT.Mazur.AffineTripleOverlapRefinementSquares
public import FLT.Mazur.SchemeOverlapRefinementTripleCocycle

/-!
# Cocycle preservation for affine categorical overlaps

Specialize the triple-overlap refinement theorem to tensor spectra, keeping
the original overlap abstract while checking the pullback comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineTripleOverlapMaps AffineTripleOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable (a : R →+* R') (b : S →+* S')
variable (w : b.comp (algebraMap R S) = (algebraMap R' S').comp a)
variable (M : (Spec (.of S)).Modules) (e : FiberProductOverlap R S M)

/-- The affine categorical cocycle survives the constructed refinement. -/
theorem refine_fiberProductCocycle (he : FiberProductCocycle R S M e) :
    FiberProductCocycle R' S' ((pullback (Spec.map (CommRingCat.ofHom b))).obj M)
      (SchemeOverlapRefinement.refine
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
        (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
        (base_square a b w) e) := by
  have hc := SchemeOverlapRefinementCocycle.refine_cocycle_of_squares
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
    (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
    (base_square a b w)
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
    (fiberProductPair R' S' (pair12 R' S')) (fiberProductPair R' S' (pair23 R' S'))
    (fiberProductPair R' S' (pair13 R' S'))
    (Spec.map (CommRingCat.ofHom (coord1 R' S')))
    (Spec.map (CommRingCat.ofHom (coord2 R' S')))
    (Spec.map (CommRingCat.ofHom (coord3 R' S')))
    (fiberProductPair_fst R' S' (pair12 R' S') (coord1 R' S') (pair12_left R' S'))
    (fiberProductPair_snd R' S' (pair12 R' S') (coord2 R' S') (pair12_right R' S'))
    (fiberProductPair_fst R' S' (pair23 R' S') (coord2 R' S') (pair23_left R' S'))
    (fiberProductPair_snd R' S' (pair23 R' S') (coord3 R' S') (pair23_right R' S'))
    (fiberProductPair_fst R' S' (pair13 R' S') (coord1 R' S') (pair13_left R' S'))
    (fiberProductPair_snd R' S' (pair13 R' S') (coord3 R' S') (pair13_right R' S'))
    (tripleSpecMap a b w)
    (tripleSpecMap_coord1 a b w) (tripleSpecMap_coord2 a b w)
    (tripleSpecMap_coord3 a b w)
    (tripleSpecMap_pair12 a b w) (tripleSpecMap_pair23 a b w)
    (tripleSpecMap_pair13 a b w) M e
    ((fiberProductCocycle_iff_scheme R S M e).mp he)
  exact (fiberProductCocycle_iff_scheme R' S' _ _).mpr hc

end FLT.Mazur.AffineGeometricOverlap
