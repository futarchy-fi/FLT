/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalFullInvariants

/-!
# Original invariant principal supports of localized full invariants

Clearing a full-relation invariant fraction gives an original invariant
numerator. Multiplying it by the original principal denominator makes its
nonvanishing open exactly the image of the local coefficient's open.
Neither coefficient is required to be admissible in an envelope.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections SchemeRelationRestriction
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : compatibleFunctions p q)
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]
local notation "W" => A.basicOpen s.val
local notation "C'" => compatibleFunctions (fst p q (Scheme.Opens.ι (A.basicOpen s.val)))
  (snd p q (Scheme.Opens.ι (A.basicOpen s.val)))

/-- Clear denominators without losing the actual full double-relation equation. -/
theorem exists_full_invariant_numerator (z : C') :
    ∃ (a : compatibleFunctions p q) (n : ℕ),
      z.val * (W).ι.appTop (s.val ^ n) = (W).ι.appTop a.val := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s ((fullEquiv p q s).symm z)
  have h := congrArg (fun t ↦ (fullEquiv p q s t).val) ha
  refine ⟨a, n, ?_⟩
  simpa only [map_mul, map_pow, RingEquiv.apply_symm_apply,
    Subring.coe_mul, Subring.coe_pow, fullEquiv_algebraMap] using h

/-- A full local invariant principal open has exactly one original invariant principal support. -/
theorem exists_full_invariant_support (z : C') :
    ∃ a : compatibleFunctions p q,
      A.basicOpen a.val = (W).ι ''ᵁ (W).toScheme.basicOpen z.val ∧
      A.basicOpen a.val ≤ W := by
  obtain ⟨a, n, ha⟩ := exists_full_invariant_numerator p q s z
  have hs : (W).toScheme.basicOpen ((W).ι.appTop (s.val ^ n)) = ⊤ := by
    rw [map_pow]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, pow_zero, Scheme.basicOpen_one]
    · rw [Scheme.basicOpen_pow _ _ hn, ← Scheme.preimage_basicOpen_top]
      exact Scheme.Opens.ι_preimage_self _
  have he : (W).toScheme.basicOpen z.val = (W).ι ⁻¹ᵁ A.basicOpen a.val := by
    rw [Scheme.preimage_basicOpen_top, ← ha, Scheme.basicOpen_mul, hs, inf_top_eq]
  refine ⟨s * a, ?_, ?_⟩
  · rw [he, Scheme.Hom.image_preimage_eq_opensRange_inf]
    change A.basicOpen (s.val * a.val) = _
    rw [Scheme.basicOpen_mul, Scheme.Opens.opensRange_ι]
  · change A.basicOpen (s.val * a.val) ≤ W
    rw [Scheme.basicOpen_mul]
    exact inf_le_left

end FLT.Mazur.SchemeRelationPrincipalLocalization
