/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontainePointSeparation

/-!
# Injectivity of compatible point lifts

Combining point separation with preservation of truncated valuations proves
the injectivity step in Fontaine's passage from point lifting to field
embeddings. Existence of the compatible lifts is an explicit hypothesis of
these lemmas; it is not asserted for a finite flat model here.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]
  (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- Compatible lifts of all integral points are automatically injective when
the final precision is greater than one half and the original precision
is greater than one. -/
theorem FF.injective_integralPoint_lifts (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    {m t : ℚ} (hm : 1 < m) (ht : 1 / 2 < t) (htm : t ≤ m)
    (f : ThreeAdicIntegers L →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (lift : (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L) →
      (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E))
    (hcompat : ∀ u, (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E t)).comp (lift u) =
      ((Ideal.Quotient.factorₐ ℤ_[3] (threeAdicValuationIdeal_antitone E htm)).comp f).comp u) :
    Function.Injective lift := by
  intro u v huv
  apply M.integralPoint_reduction_injective L hM ht
  ext x
  apply Ideal.Quotient.eq.mpr
  have hq := (hcompat u).symm.trans
    ((congrArg (fun w ↦
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E t)).comp w) huv).trans (hcompat v))
  have hx := DFunLike.congr_fun hq x
  have hk : u x - v x ∈ RingHom.ker
      (((Ideal.Quotient.factorₐ ℤ_[3]
        (threeAdicValuationIdeal_antitone E htm)).comp f).toRingHom) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hx
  rwa [ker_factor_comp_quotientMap E L hm htm f] at hk

/-- At Fontaine precision `m > 3/2`, lifts agreeing after a loss of one unit
of precision give an embedding of the sets of integral points. -/
theorem FF.nonempty_integralPoint_embedding_of_lifts (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    {m : ℚ} (hm : 3 / 2 < m)
    (f : ThreeAdicIntegers L →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (hlift : ∀ u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
        (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
          ((Ideal.Quotient.factorₐ ℤ_[3]
            (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp f).comp u) :
    Nonempty ((M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L) ↪
      (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E)) := by
  choose lift hcompat using hlift
  exact ⟨⟨lift, M.injective_integralPoint_lifts L E hM (by linarith) (by linarith)
    (show m - 1 ≤ m by linarith) f lift hcompat⟩⟩

end ThreeAdicPlan
