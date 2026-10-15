/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphSpecialFiber

/-!
# The actual graph special fiber is a split square-zero extension

The original source, rather than a chosen replacement action, gives a
section of the special-fiber reduction onto the original split node. The
remaining kernel has square zero and is retained in the construction.
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
local notation "N" => ChartRing (0 : R)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "r" => completeIdentityFirstGraphReduction K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "I" => completeIdentityFirstGraphParameterIdeal K n h i
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
/-- The existing graph ring structure, cached for this construction. -/
local instance completeIdentityFirstGraphFiberSplitCommRing : CommRing (E) := inferInstance
/-- The existing quotient ring structure, cached for the fiber calculations. -/
local instance completeIdentityFirstGraphFiberSplitQuotientCommRing : CommRing (Q) :=
  inferInstance

/-- The literal quotient map into the original graph special fiber. -/
def completeIdentityFirstGraphFiberQuotient : (E) →+* (Q) := Ideal.Quotient.mk (I)

local notation "q" => completeIdentityFirstGraphFiberQuotient K n h i

/-- Reduction of the literal graph special fiber onto the unchanged original split node. -/
def completeIdentityFirstGraphFiberReduction : (Q) →+* (N) :=
  Ideal.Quotient.lift (I) (r) (completeIdentityFirstGraphParameterIdeal_le K n h i)

/-- The fiber reduction retains the full original reduction map. -/
theorem completeIdentityFirstGraphFiberReduction_mk (z : E) :
    completeIdentityFirstGraphFiberReduction K n h i ((q) z) = (r) z := rfl

/-- The original source kills precisely the required reduction kernel after passing to the fiber. -/
theorem completeIdentityFirstGraphFiberSource_kernel :
    RingHom.ker (firstNodeReduction (R)) ≤ RingHom.ker ((q).comp (s).toRingHom) := by
  let _ : CommRing (E) := inferInstance
  let _ : CommRing ((E) ⧸ (I)) := inferInstance
  intro z hz
  obtain ⟨w, hw⟩ := (firstNodeReduction_zero_iff (R) z).mp hz
  change (q) ((s) z) = (0 : Q)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨(s) w, ?_⟩
  rw [← map_mul]
  exact congrArg (s) (hw.symm.trans (Algebra.smul_def (e) w))

/-- The unchanged source induces a section on the original reduced node. -/
def completeIdentityFirstGraphFiberSection : (N) →+* (Q) :=
  (firstNodeReduction (R)).liftOfSurjective (firstNodeReduction_surjective (R))
    ⟨(q).comp (s).toRingHom, completeIdentityFirstGraphFiberSource_kernel K n h i⟩

/-- This section is obtained from every actual original node lift. -/
theorem completeIdentityFirstGraphFiberSection_reduction (z : B) :
    completeIdentityFirstGraphFiberSection K n h i (firstNodeReduction (R) z) =
      (q) ((s) z) :=
  (firstNodeReduction (R)).liftOfSurjective_comp_apply
    (firstNodeReduction_surjective (R)) _ z

/-- The original source section is a genuine right inverse to the fiber reduction. -/
theorem completeIdentityFirstGraphFiberSection_rightInverse :
    Function.RightInverse (completeIdentityFirstGraphFiberSection K n h i)
      (completeIdentityFirstGraphFiberReduction K n h i) := by
  intro z
  obtain ⟨w, rfl⟩ := firstNodeReduction_surjective (R) z
  rw [completeIdentityFirstGraphFiberSection_reduction,
    completeIdentityFirstGraphFiberReduction_mk, completeIdentityFirstGraphReduction_source]

/-- The exact special-fiber reduction is surjective. -/
theorem completeIdentityFirstGraphFiberReduction_surjective :
    Function.Surjective (completeIdentityFirstGraphFiberReduction K n h i) :=
  (completeIdentityFirstGraphFiberSection_rightInverse K n h i).surjective

/-- The entire residual special-fiber kernel, not just its generators, has square zero. -/
theorem completeIdentityFirstGraphFiberReduction_kernel_mul (z w : Q)
    (hz : completeIdentityFirstGraphFiberReduction K n h i z = 0)
    (hw : completeIdentityFirstGraphFiberReduction K n h i w = 0) : z * w = (0 : Q) := by
  let _ : CommRing (E) := inferInstance
  let _ : CommRing ((E) ⧸ (I)) := inferInstance
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hab := completeIdentityFirstGraphReduction_kernel_mul K n h i a b hz hw
  exact ((q).map_mul a b).symm.trans ((congrArg (q) hab).trans (q).map_zero)

/-- Every fiber function splits into an original node part and its square-zero error. -/
theorem completeIdentityFirstGraphFiber_decomposition (z : Q) :
    ∃ w : Q, completeIdentityFirstGraphFiberReduction K n h i w = 0 ∧
      z = completeIdentityFirstGraphFiberSection K n h i
        (completeIdentityFirstGraphFiberReduction K n h i z) + w := by
  refine ⟨z - completeIdentityFirstGraphFiberSection K n h i
    (completeIdentityFirstGraphFiberReduction K n h i z), ?_, ?_⟩
  · change (completeIdentityFirstGraphFiberReduction K n h i).toAddMonoidHom _ = 0
    rw [map_sub]
    change completeIdentityFirstGraphFiberReduction K n h i z -
      completeIdentityFirstGraphFiberReduction K n h i
        (completeIdentityFirstGraphFiberSection K n h i
          (completeIdentityFirstGraphFiberReduction K n h i z)) = 0
    rw [completeIdentityFirstGraphFiberSection_rightInverse, sub_self]
  · abel

end FLT.Mazur.PolygonInfinitesimalStages
