/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelRecovery
public import FLT.Mazur.OneGonAdicSubgroupReductionIdeal

/-!
# Every adic order retains the enlarged smooth model's full ideal

The coefficient enlargement used for smooth factorization also recovers
every original finite adic character embedding as a Cartesian pullback.
The comparison preserves its full closed-subscheme ideal at each order.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- Every finite-order ideal is pulled back from the same enlarged full model ideal. -/
theorem smoothModelEmbedding_reduction_ideal (m : ℕ) :
    (stageCurveMap I t ht (initialRootsHom n I t ht) m).ker =
      (smoothModelEmbedding I t ht n).left.ker.comap
        (coefficientMorphism (S := StageRing I m) t ≫ smoothModelCurveRecovery I t ht n) := by
  rw [Scheme.IdealSheafData.comap_comp, ← smoothModelEmbedding_recovery_ideal]
  exact (canonicalFiniteSubgroup_reduction_ideal I t ht n m).symm

/-- Every original finite character embedding is recovered from the enlarged smooth model. -/
theorem smoothModelEmbedding_reduction_isPullback (m : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (FiniteCharacterAdicElements.reduction (G := ZMod n) I m)) ≫
      smoothModelSourceRecovery I t ht n)
      (stageCurveMap I t ht (initialRootsHom n I t ht) m)
      (smoothModelEmbedding I t ht n).left
      (coefficientMorphism (S := StageRing I m) t ≫ smoothModelCurveRecovery I t ht n) :=
  (stageCurveMap_isPullback I t ht n (initialRootsHom n I t ht) m).paste_horiz
    (smoothModelEmbedding_recovery_isPullback I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
