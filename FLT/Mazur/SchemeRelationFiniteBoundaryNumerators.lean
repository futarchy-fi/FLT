/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalBoundaryNumerator

/-!
# One exponent for finitely many full invariant boundary numerators

The exponent is constructed from the actual local lifts. It clears both
their relation equations and their exact boundary equations simultaneously.
There is no uniformity assertion for an infinite tower of rank orders.
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

/-- Finite principal boundary lifts have exact invariant numerators at one common exponent. -/
theorem exists_common_boundary_numerators
    (v : ∀ j, coefficients p q (U j) (hU j)) (t : Γ(Y, ⊤))
    (hv : ∀ j, (principalPullbackMap i (r j).val).appTop (v j).val =
      (Y.basicOpen (i.appTop (r j).val)).ι.appTop t) :
    ∃ (N : ℕ) (w : ι → compatibleFunctions p q),
      (∀ j, i.appTop (w j).val = (i.appTop (r j).val) ^ N * t) ∧
      ∀ j, (U j).ι.appTop (w j).val =
        ((U j).ι.appTop (r j).val) ^ N * (v j).val := by
  classical
  let _ := Fintype.ofFinite ι
  choose n w hb he using fun j ↦ exists_boundary_numerator p q (r j) i (v j) t (hv j)
  let N := Finset.univ.sup n
  have hn (j : ι) : n j ≤ N := Finset.le_sup (Finset.mem_univ j)
  refine ⟨N, fun j ↦ r j ^ (N - n j) * w j, ?_, ?_⟩
  · intro j
    change i.appTop ((r j).val ^ (N - n j) * (w j).val) = _
    rw [map_mul, map_pow, hb, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hn j)]
  · intro j
    change (U j).ι.appTop ((r j).val ^ (N - n j) * (w j).val) = _
    rw [map_mul, map_pow, he, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hn j)]

end FLT.Mazur.SchemeRelationPrincipalBoundaryNumerator
