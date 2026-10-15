/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphNilradical

/-!
# The special fiber of the unchanged finite node graph

Keep the literal parameter ideal rather than the larger nilradical. The
special fiber is reduced exactly when the original source is surjective.
The parameter-conductor calculation proves this without assuming flatness.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "r" => completeIdentityFirstGraphReduction K n h i
/-- The existing graph ring structure, cached for this construction. -/
local instance completeIdentityFirstGraphSpecialFiberSourceCommRing : CommRing (E) := inferInstance
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "t" => (s) (algebraMap (S) (B) (e))

/-- The actual coefficient special-fiber ideal in the unchanged original finite graph. -/
def completeIdentityFirstGraphParameterIdeal : Ideal (E) := Ideal.span {t}

/-- The graph's actual special fiber, retaining any additional nilpotents at the node. -/
def completeIdentityFirstGraphSpecialFiber :=
  (E) ⧸ completeIdentityFirstGraphParameterIdeal K n h i

/-- The literal quotient ring structure on the actual special fiber. -/
instance completeIdentityFirstGraphSpecialFiberCommRing :
    CommRing (completeIdentityFirstGraphSpecialFiber K n h i) :=
  inferInstanceAs (CommRing ((E) ⧸ completeIdentityFirstGraphParameterIdeal K n h i))

/-- The original parameter dies in the constructed node reduction. -/
theorem completeIdentityFirstGraphReduction_parameter : (r) (t) = 0 := by
  rw [completeIdentityFirstGraphReduction_source, firstNodeReduction, ringMap_scalar]
  change algebraMap (R) (ChartRing (0 : R)) (reduction (R) 1 (e)) = 0
  rw [reduction_parameter, map_zero]

/-- The literal parameter ideal lies in the full reduction kernel. -/
theorem completeIdentityFirstGraphParameterIdeal_le :
    completeIdentityFirstGraphParameterIdeal K n h i ≤ RingHom.ker (r) := by
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
    (completeIdentityFirstGraphReduction_parameter K n h i))

/-- Parameter multiplication on the graph agrees with its unchanged ambient branch action. -/
theorem completeIdentityFirstGraph_parameter_mul (z : E) :
    ((t) * z).val = (e) • z.val := by
  change (t).val * z.val = _
  rw [completeIdentityFirstGraphSource_apply, AlgHom.commutes, Algebra.smul_def]

/-- Every parameter multiple in the actual graph comes from the original source node. -/
theorem completeIdentityFirstGraph_parameter_source (z : E) :
    ∃ w : B, (s) w = (t) * z := by
  have hz : z.val ∈ completeIdentityFirstGraphAlgebra K n h i := by
    rw [← completeIdentityFirstErrorAlgebra_eq_graph]
    exact z.property
  obtain ⟨w, hw⟩ := completeIdentityFirstGraphAlgebra_parameter K n h i z.val hz
  refine ⟨w, Subtype.ext ?_⟩
  rw [completeIdentityFirstGraph_parameter_mul, completeIdentityFirstGraphSource_apply]
  exact hw

/-- If the special fiber is reduced, every graph function already comes from its source. -/
theorem completeIdentityFirstGraphSource_surjective_of_reduced
    [IsReduced (completeIdentityFirstGraphSpecialFiber K n h i)] :
    Function.Surjective (s) := by
  let _ : IsReduced ((E) ⧸ completeIdentityFirstGraphParameterIdeal K n h i) :=
    inferInstanceAs (IsReduced (completeIdentityFirstGraphSpecialFiber K n h i))
  have hk := SquareZeroReductionKernel.ker_le_of_quotient_reduced (r)
    (fun z hz ↦ completeIdentityFirstGraphReduction_kernel_mul K n h i z z hz hz)
    (completeIdentityFirstGraphParameterIdeal K n h i)
  intro z
  obtain ⟨a, ha⟩ := firstNodeReduction_surjective (R) ((r) z)
  have hd : z - (s) a ∈ RingHom.ker (r) := by
    change (r) (z - (s) a) = 0
    change (r).toAddMonoidHom (z - (s) a) = 0
    rw [map_sub]
    change (r) z - (r) ((s) a) = 0
    rw [completeIdentityFirstGraphReduction_source, ha, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp (hk hd)
  obtain ⟨w, hw⟩ := completeIdentityFirstGraph_parameter_source K n h i v
  refine ⟨a + w, ?_⟩
  rw [map_add, hw, ← hv]
  abel

/-- A surjective original source leaves no reduction kernel beyond the parameter ideal. -/
theorem completeIdentityFirstGraphReduction_ker_le_parameter
    (hs : Function.Surjective (s)) :
    RingHom.ker (r) ≤ completeIdentityFirstGraphParameterIdeal K n h i := by
  intro z hz
  obtain ⟨w, rfl⟩ := hs z
  have hw : firstNodeReduction (R) w = 0 :=
    (completeIdentityFirstGraphReduction_source K n h i w).symm.trans hz
  obtain ⟨a, ha⟩ := (firstNodeReduction_zero_iff (R) w).mp hw
  apply Ideal.mem_span_singleton.mpr
  refine ⟨(s) a, ?_⟩
  rw [← map_mul]
  exact congrArg (s) (ha.symm.trans (Algebra.smul_def (e) a))

/-- Reducedness of the literal special fiber is the exact remaining source-isomorphism test. -/
theorem completeIdentityFirstGraphSpecialFiber_reduced_iff :
    IsReduced (completeIdentityFirstGraphSpecialFiber K n h i) ↔
      Function.Surjective (s) := by
  constructor
  · intro hi
    let _ := hi
    exact completeIdentityFirstGraphSource_surjective_of_reduced K n h i
  · intro hs
    let _ := splitNodeBranchPair_isReduced (R)
    exact (SquareZeroReductionKernel.quotient_reduced_iff (r)
      (fun z hz ↦ completeIdentityFirstGraphReduction_kernel_mul K n h i z z hz hz)
      (completeIdentityFirstGraphParameterIdeal K n h i)
      (completeIdentityFirstGraphParameterIdeal_le K n h i)).mpr
        (completeIdentityFirstGraphReduction_ker_le_parameter K n h i hs)

end FLT.Mazur.PolygonInfinitesimalStages
