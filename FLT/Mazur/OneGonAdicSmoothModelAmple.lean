/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelCyclicity
public import FLT.Mazur.ArithmeticOneGonChangedSubgroupAmple

/-!
# Ample cyclic level on the actual finite coefficient model

The descended subgroup is cyclic, and its positive Cartier divisor is ample
on the same generalized one-gon. Exact recovery of the whole-curve ideal is
retained over the original complete ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The actual descended cyclic subgroup has an ample full Cartier ideal. -/
theorem smoothModelFiniteSubgroup_isAmple : (smoothModelFiniteSubgroup I t ht n).IsAmple :=
  ArithmeticOneGonSubgroupAmple.isAmple_after_baseChange (algebraicParameter I t ht n)
    (algebraicParameter_complementaryUnit I t ht n) (smoothModelBaseMap I t ht n)
    (smoothModelFiniteSubgroup I t ht n) (NeZero.pos n)
    (smoothModelFiniteSubgroup_relativeCartier I t ht n).1

/-- An ample cyclic level exists on the same finite-presentation algebraic model. -/
theorem smoothModel_ample_cyclic :
    ∃ H : (smoothModelCurve I t ht n).FiniteSubgroup n,
      H.IsCyclic ∧ H.IsAmple ∧ ∃ e : H.carrier ≅ smoothModelCarrier I t ht n,
      H.curveMap = e.hom ≫ smoothModelEmbedding I t ht n ∧
      (canonicalFiniteSubgroup I t ht n).ideal =
        H.ideal.comap (smoothModelCurveRecovery I t ht n) := by
  refine ⟨smoothModelFiniteSubgroup I t ht n, smoothModelFiniteSubgroup_isCyclic I t ht n,
    smoothModelFiniteSubgroup_isAmple I t ht n, Iso.refl _, ?_,
    smoothModelFiniteSubgroup_recovery_ideal I t ht n⟩
  simpa only [Iso.refl_hom, Category.id_comp] using smoothModelFiniteSubgroup_curveMap I t ht n


end FLT.Mazur.OneGonAdicCharacterTower
