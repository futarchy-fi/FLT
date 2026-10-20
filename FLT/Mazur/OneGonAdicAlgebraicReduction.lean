/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicAlgebraicEmbedding
public import FLT.Mazur.OneGonAdicSubgroupReductionIdeal

/-!
# Algebraic recovery retains all full adic reduction ideals

Every finite-order ideal of the actual canonical subgroup is pulled back from
the constructed finite-coefficient closed embedding on the whole cubic.
This compares the full ideals, rather than radicals or geometric point sets.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- Every original finite-order whole-cubic ideal comes from the same algebraic model ideal. -/
theorem algebraicEmbedding_reduction_ideal (m : ℕ) :
    (stageCurveMap I t ht (initialRootsHom n I t ht) m).ker =
      (algebraicEmbedding I t ht n).ker.comap
        (coefficientMorphism (S := StageRing I m) t ≫ algebraicProjection I t ht n) := by
  rw [Scheme.IdealSheafData.comap_comp, ← algebraicEmbedding_ideal]
  exact (canonicalFiniteSubgroup_reduction_ideal I t ht n m).symm

/-- Every original finite character embedding is a Cartesian pullback of the algebraic model. -/
theorem algebraicEmbedding_reduction_isPullback (m : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (FiniteCharacterAdicElements.reduction (G := ZMod n) I m)) ≫
      Spec.map (CommRingCat.ofHom
        (OneGonFiniteCoefficientCoordinates.modelInclusion t 1
          (canonicalCoordinates I t ht n) (algebraicSupport I t ht n))))
      (stageCurveMap I t ht (initialRootsHom n I t ht) m)
      (algebraicEmbedding I t ht n)
      (coefficientMorphism (S := StageRing I m) t ≫ algebraicProjection I t ht n) :=
  (stageCurveMap_isPullback I t ht n (initialRootsHom n I t ht) m).paste_horiz
    (algebraicEmbedding_isPullback I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
