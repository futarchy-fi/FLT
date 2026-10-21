/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedStage

/-!
# The literal finite ring for three independently supplied stages

The supremum of the three actual stage subalgebras is finite type and contains
each supplied stage. In particular no functorial choice of smooth stages is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u v : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (k : (CoefficientStage (base I t ht n v))ᵒᵖ)

/-- The literal supremum of the three independently supplied stage rings. -/
abbrev tripleBase : Subalgebra ℤ R :=
  (stageBase I t ht n s i ⊔ stageBase I t ht n u j) ⊔ stageBase I t ht n v k

instance tripleBase_finiteType : Algebra.FiniteType ℤ (tripleBase I t ht n s u v i j k) := by
  apply (tripleBase I t ht n s u v i j k).fg_iff_finiteType.mp
  exact (((stageBase I t ht n s i).fg_iff_finiteType.mpr
    (stageBase_finiteType I t ht n s i)).sup
      ((stageBase I t ht n u j).fg_iff_finiteType.mpr
        (stageBase_finiteType I t ht n u j))).sup
          ((stageBase I t ht n v k).fg_iff_finiteType.mpr (stageBase_finiteType I t ht n v k))

/-- The first actual stage is contained in the triple ring. -/
theorem stage_le_triple_first : stageBase I t ht n s i ≤ tripleBase I t ht n s u v i j k :=
  le_sup_left.trans le_sup_left

/-- The second actual stage is contained in the triple ring. -/
theorem stage_le_triple_second : stageBase I t ht n u j ≤ tripleBase I t ht n s u v i j k :=
  le_sup_right.trans le_sup_left

/-- The third actual stage is contained in the triple ring. -/
theorem stage_le_triple_third : stageBase I t ht n v k ≤ tripleBase I t ht n s u v i j k :=
  le_sup_right

/-- The first support is contained in the actual triple ring. -/
theorem base_le_triple_first : base I t ht n s ≤ tripleBase I t ht n s u v i j k :=
  i.unop.property.1.trans (stage_le_triple_first I t ht n s u v i j k)

/-- The second support is contained in the actual triple ring. -/
theorem base_le_triple_second : base I t ht n u ≤ tripleBase I t ht n s u v i j k :=
  j.unop.property.1.trans (stage_le_triple_second I t ht n s u v i j k)

/-- The third support is contained in the actual triple ring. -/
theorem base_le_triple_third : base I t ht n v ≤ tripleBase I t ht n s u v i j k :=
  k.unop.property.1.trans (stage_le_triple_third I t ht n s u v i j k)

/-- The first pairwise common ring maps to the literal triple ring. -/
theorem common_le_triple_first_second :
    commonBase I t ht n s u i j ≤ tripleBase I t ht n s u v i j k := le_sup_left

/-- The second pairwise common ring maps to the same triple ring. -/
theorem common_le_triple_second_third :
    commonBase I t ht n u v j k ≤ tripleBase I t ht n s u v i j k :=
  sup_le (stage_le_triple_second I t ht n s u v i j k)
    (stage_le_triple_third I t ht n s u v i j k)

/-- The first and third pairwise common ring maps to the same triple ring. -/
theorem common_le_triple_first_third :
    commonBase I t ht n s v i k ≤ tripleBase I t ht n s u v i j k :=
  sup_le (stage_le_triple_first I t ht n s u v i j k)
    (stage_le_triple_third I t ht n s u v i j k)

end FLT.Mazur.OneGonAdicIndependentModel
