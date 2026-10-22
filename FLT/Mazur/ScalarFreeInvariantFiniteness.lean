/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarOrbitFiniteEquations

/-!
# Finite invariant defects from finite original source coordinates

Weighted trace splits the full fixed-ring inclusion over the original scalar
ring. Finiteness of the original source therefore constructs finiteness of
both the fixed ring and its full scalar cokernel. No Noetherian assumption or
division by the group order is used. Source finiteness remains an input.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type*) [Group G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A]
local notation "S" => invariantRing G A

/-- The full module defect of the prescribed scalar image inside the fixed ring. -/
abbrev scalarCokernel := S ⧸ LinearMap.range (Algebra.linearMap R S)

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- The trace retraction is linear over the unchanged original scalar ring. -/
theorem exists_scalar_retraction :
    ∃ r : A →ₗ[R] S, ∀ s : S, r s.val = s := by
  obtain ⟨r, hr⟩ := exists_invariant_linear_retraction G hfree
  exact ⟨r.restrictScalars R, hr⟩

/-- Finite original source coordinates give finite full invariant coordinates. -/
theorem invariant_finite_of_source [Module.Finite R A] : Module.Finite R S := by
  obtain ⟨r, hr⟩ := exists_scalar_retraction G R A hfree
  exact Module.Finite.of_surjective r (fun s ↦ ⟨s.val, hr s⟩)

/-- The entire original scalar cokernel is finite, including all nilpotent classes. -/
theorem scalarCokernel_finite [Module.Finite R A] : Module.Finite R (scalarCokernel G R A) := by
  let _ := invariant_finite_of_source G R A hfree
  infer_instance

/-- Finite original source coordinates supply finite equations for the full comparison. -/
theorem comparison_ker_fg_of_source [Module.Finite R A] :
    (RingHom.ker (comparison G R A).toRingHom).FG := by
  let _ := invariant_finite_of_source G R A hfree
  exact comparison_ker_fg G R A hfree

end FLT.Mazur.ScalarOrbitTensorComparison
