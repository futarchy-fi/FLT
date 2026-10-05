/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapRefinement
public import FLT.Mazur.AffineFiberProductPairTransport
public import FLT.Mazur.SchemeOverlapRefinement

/-!
# Scheme squares for affine triple-overlap refinement

The spectrum of the triple tensor map respects each coordinate and each
categorical pair projection. The pair squares follow from the universal
property of the double fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.AffineTripleOverlapRefinement
open AffineOverlapTensor AffineTripleOverlapMaps AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable (a : R →+* R') (b : S →+* S')
variable (w : b.comp (algebraMap R S) = (algebraMap R' S').comp a)

/-- The map from the refined triple spectrum to the original triple spectrum. -/
def tripleSpecMap : Spec (.of (Triple R' S')) ⟶ Spec (.of (Triple R S)) :=
  Spec.map (CommRingCat.ofHom (tripleMap a b w))

/-- A coordinate ring square induces the contravariant spectrum square. -/
theorem tripleSpecMap_coordinate (c : S →+* Triple R S) (c' : S' →+* Triple R' S')
    (hc : (tripleMap a b w).comp c = c'.comp b) :
    tripleSpecMap a b w ≫ Spec.map (CommRingCat.ofHom c) =
      Spec.map (CommRingCat.ofHom c') ≫ Spec.map (CommRingCat.ofHom b) := by
  rw [← Spec.map_comp]
  exact spec_comp c (tripleMap a b w) (c'.comp b) hc

/-- The first coordinate spectrum square. -/
theorem tripleSpecMap_coord1 :
    tripleSpecMap a b w ≫ Spec.map (CommRingCat.ofHom (coord1 R S)) =
      Spec.map (CommRingCat.ofHom (coord1 R' S')) ≫ Spec.map (CommRingCat.ofHom b) :=
  tripleSpecMap_coordinate a b w _ _ (tripleMap_coord1 a b w)

/-- The middle coordinate spectrum square. -/
theorem tripleSpecMap_coord2 :
    tripleSpecMap a b w ≫ Spec.map (CommRingCat.ofHom (coord2 R S)) =
      Spec.map (CommRingCat.ofHom (coord2 R' S')) ≫ Spec.map (CommRingCat.ofHom b) :=
  tripleSpecMap_coordinate a b w _ _ (tripleMap_coord2 a b w)

/-- The last coordinate spectrum square. -/
theorem tripleSpecMap_coord3 :
    tripleSpecMap a b w ≫ Spec.map (CommRingCat.ofHom (coord3 R S)) =
      Spec.map (CommRingCat.ofHom (coord3 R' S')) ≫ Spec.map (CommRingCat.ofHom b) :=
  tripleSpecMap_coordinate a b w _ _ (tripleMap_coord3 a b w)

include w in
/-- The base spectrum square supplied by the ring square. -/
theorem base_square :
    Spec.map (CommRingCat.ofHom (algebraMap R' S')) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom w.symm)

/-- A pair square follows from its two coordinate squares. -/
theorem tripleSpecMap_pair (t : S ⊗[R] S →ₐ[R] Triple R S)
    (t' : S' ⊗[R'] S' →ₐ[R'] Triple R' S')
    (i j : S →+* Triple R S) (i' j' : S' →+* Triple R' S')
    (hi : t.toRingHom.comp (left R S) = i) (hj : t.toRingHom.comp (right R S) = j)
    (hi' : t'.toRingHom.comp (left R' S') = i')
    (hj' : t'.toRingHom.comp (right R' S') = j')
    (wi : (tripleMap a b w).comp i = i'.comp b)
    (wj : (tripleMap a b w).comp j = j'.comp b) :
    tripleSpecMap a b w ≫ fiberProductPair R S t =
      fiberProductPair R' S' t' ≫ SchemeOverlapRefinement.overlapMap
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
        (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
        (base_square a b w) := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, SchemeOverlapRefinement.overlapMap_fst,
      fiberProductPair_fst R S t i hi]
    rw [← Category.assoc, fiberProductPair_fst R' S' t' i' hi']
    exact tripleSpecMap_coordinate a b w i i' wi
  · simp only [Category.assoc, SchemeOverlapRefinement.overlapMap_snd,
      fiberProductPair_snd R S t j hj]
    rw [← Category.assoc, fiberProductPair_snd R' S' t' j' hj']
    exact tripleSpecMap_coordinate a b w j j' wj

/-- Refinement commutes with categorical pair 12. -/
theorem tripleSpecMap_pair12 :
    tripleSpecMap a b w ≫ fiberProductPair R S (pair12 R S) =
      fiberProductPair R' S' (pair12 R' S') ≫ SchemeOverlapRefinement.overlapMap
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
        (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
        (base_square a b w) :=
  tripleSpecMap_pair a b w _ _ (coord1 R S) (coord2 R S)
    (coord1 R' S') (coord2 R' S') (pair12_left R S) (pair12_right R S)
    (pair12_left R' S') (pair12_right R' S')
    (tripleMap_coord1 a b w) (tripleMap_coord2 a b w)

/-- Refinement commutes with categorical pair 23. -/
theorem tripleSpecMap_pair23 :
    tripleSpecMap a b w ≫ fiberProductPair R S (pair23 R S) =
      fiberProductPair R' S' (pair23 R' S') ≫ SchemeOverlapRefinement.overlapMap
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
        (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
        (base_square a b w) :=
  tripleSpecMap_pair a b w _ _ (coord2 R S) (coord3 R S)
    (coord2 R' S') (coord3 R' S') (pair23_left R S) (pair23_right R S)
    (pair23_left R' S') (pair23_right R' S')
    (tripleMap_coord2 a b w) (tripleMap_coord3 a b w)

/-- Refinement commutes with categorical pair 13. -/
theorem tripleSpecMap_pair13 :
    tripleSpecMap a b w ≫ fiberProductPair R S (pair13 R S) =
      fiberProductPair R' S' (pair13 R' S') ≫ SchemeOverlapRefinement.overlapMap
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R' S')))
        (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b))
        (base_square a b w) :=
  tripleSpecMap_pair a b w _ _ (coord1 R S) (coord3 R S)
    (coord1 R' S') (coord3 R' S') (pair13_left R S) (pair13_right R S)
    (pair13_left R' S') (pair13_right R' S')
    (tripleMap_coord1 a b w) (tripleMap_coord3 a b w)

end FLT.Mazur.AffineTripleOverlapRefinement
