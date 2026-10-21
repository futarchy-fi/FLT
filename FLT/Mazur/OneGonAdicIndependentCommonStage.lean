/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentStageModel

/-!
# A common finite ring for independent support and smooth-stage choices

The supremum of the two actual stage subalgebras is finite type. It contains
both supports and supplies literal transition maps in both coefficient diagrams.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)

/-- The common ring consists of the two actual stage subalgebras and their ring operations. -/
abbrev commonBase : Subalgebra ℤ R := stageBase I t ht n s i ⊔ stageBase I t ht n u j

instance commonBase_finiteType : Algebra.FiniteType ℤ (commonBase I t ht n s u i j) := by
  apply (commonBase I t ht n s u i j).fg_iff_finiteType.mp
  exact ((stageBase I t ht n s i).fg_iff_finiteType.mpr (stageBase_finiteType I t ht n s i)).sup
    ((stageBase I t ht n u j).fg_iff_finiteType.mpr (stageBase_finiteType I t ht n u j))

instance commonBase_finitePresentation :
    Algebra.FinitePresentation ℤ (commonBase I t ht n s u i j) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- The original left support ring embeds in the common stage. -/
theorem base_le_common_left : base I t ht n s ≤ commonBase I t ht n s u i j :=
  i.unop.property.1.trans le_sup_left

/-- The original right support ring embeds in the same common stage. -/
theorem base_le_common_right : base I t ht n u ≤ commonBase I t ht n s u i j :=
  j.unop.property.1.trans le_sup_right

/-- The common ring is a stage in the left coefficient system. -/
def commonLeft : (CoefficientStage (base I t ht n s))ᵒᵖ :=
  Opposite.op ⟨commonBase I t ht n s u i j,
    base_le_common_left I t ht n s u i j, inferInstance⟩

/-- The same ring is a stage in the right coefficient system. -/
def commonRight : (CoefficientStage (base I t ht n u))ᵒᵖ :=
  Opposite.op ⟨commonBase I t ht n s u i j,
    base_le_common_right I t ht n s u i j, inferInstance⟩

/-- The actual transition to the first supplied smooth stage. -/
def commonToLeft : commonLeft I t ht n s u i j ⟶ i :=
  (homOfLE (show i.unop ≤ (commonLeft I t ht n s u i j).unop from
    (le_sup_left : stageBase I t ht n s i ≤ commonBase I t ht n s u i j))).op

/-- The actual transition to the second supplied smooth stage. -/
def commonToRight : commonRight I t ht n s u i j ⟶ j :=
  (homOfLE (show j.unop ≤ (commonRight I t ht n s u i j).unop from
    (le_sup_right : stageBase I t ht n u j ≤ commonBase I t ht n s u i j))).op

/-- Independent presentations retain the same original smoothing parameter in the common ring. -/
theorem common_parameter_eq :
    Subalgebra.inclusion (base_le_common_left I t ht n s u i j) (parameter I t ht n s) =
      Subalgebra.inclusion (base_le_common_right I t ht n s u i j)
        (parameter I t ht n u) := by
  apply Subtype.ext
  rfl

end FLT.Mazur.OneGonAdicIndependentModel
