/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationFiniteBoundaryNumerators
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Constructed full boundary lifts from finite invariant principal patches

Local lifts need only have the same prescribed boundary value. Clearing
denominators and a unit-ideal equation construct a global invariant lift;
no equality of the initial lifts on overlaps is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationPrincipalBoundaryNumerator
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {D X Y : Scheme.{0}} (p q : D ⟶ X) [IsAffine X]
  [CompactSpace D] [QuasiSeparatedSpace D] (i : Y ⟶ X) [IsAffine Y]
  {ι : Type*} [Finite ι] (r : ι → compatibleFunctions p q)
local notation "U" j => X.basicOpen (r j).val
local notation "hU" j => compatibleFunctions_basicOpen p q (r j)

/-- A finite invariant unit-ideal family assembles unrelated local boundary lifts. -/
theorem exists_boundary_lift_of_span
    (hr : Ideal.span (Set.range r) = ⊤)
    (v : ∀ j, coefficients p q (U j) (hU j)) (t : Γ(Y, ⊤))
    (hv : ∀ j, (principalPullbackMap i (r j).val).appTop (v j).val =
      (Y.basicOpen (i.appTop (r j).val)).ι.appTop t) :
    ∃ w : compatibleFunctions p q, i.appTop w.val = t := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨N, w, hb, _⟩ := exists_common_boundary_numerators p q i r v t hv
  have hN : Ideal.span (Set.range fun j ↦ r j ^ N) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def] using
      Ideal.span_pow_eq_top (Set.range r) hr N
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : compatibleFunctions p q) ∈ Ideal.span (Set.range fun j ↦ r j ^ N) by
      rw [hN]; trivial)
  let b : compatibleFunctions p q →+* Γ(Y, ⊤) :=
    i.appTop.hom.comp (compatibleFunctions p q).subtype
  refine ⟨∑ j, c j * w j, ?_⟩
  change b (∑ j, c j * w j) = t
  have hb' (j : ι) : b (w j) = b (r j) ^ N * t := hb j
  have hc' : ∑ j, b (c j) * b (r j) ^ N = 1 := by
    simpa only [map_sum, map_mul, map_pow, map_one] using congrArg b hc
  simp only [map_sum, map_mul, hb', ← mul_assoc, ← Finset.sum_mul, hc', one_mul]

end FLT.Mazur.SchemeRelationPrincipalBoundaryNumerator
