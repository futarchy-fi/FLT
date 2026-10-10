/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorSmoothOpen
public import FLT.Mazur.WeierstrassDividedFiniteYBoundary

/-!
# The full original smooth open through every finite local contraction

The initial Rees modification is unchanged outside its center. All further
whole steps preserve every point above the original smooth locus. Composing
these full comparisons gives the actual finite contraction isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ} (d : Data W π k)
open WeierstrassIntegralChart

include hπ in
/-- The initial actual affine contraction is unchanged over the full original smooth open. -/
theorem initialToAffine_originalSmooth_isIso :
    IsIso (initialToAffine d ∣_ (chartStructure W 2).smoothLocus) := by
  apply SchemeUnchangedOpen.isIso_precomp (initialExteriorIso d)
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro p hp
  have hn := modificationCenter_not_le_of_smooth W (π ^ k) d.b3 d.b4
    d.factor3 d.factor4 p hp
  change ¬ ∀ f, f ∈ _ → f ∈ p.asIdeal at hn
  push Not at hn
  obtain ⟨f, hf, hfp⟩ := hn
  refine ⟨(PrincipalAffineRefinement.inclusion f).opensRange, ?_, ?_⟩
  · change p ∈ Set.range (PrincipalAffineRefinement.inclusion f)
    rwa [PrincipalAffineRefinement.range_inclusion]
  · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (WeierstrassModificationReesCoordinates.originalOpen_isPullback W (π ^ k)
        d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ) f hf)

variable {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))

omit [IsBezout R] in
/-- Every finite local step preserves the complete preimage of the original smooth open. -/
theorem finiteStep_originalSmooth_isIso (j : ℕ) (hj : j + 1 ≤ n) :
    IsIso (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ∣_
      finiteToAffine hπ data j (Nat.le_of_succ_le hj) ⁻¹ᵁ
        (chartStructure W 2).smoothLocus) :=
  Exterior.step_originalSmooth_isIso hπ _ _ _
    (finiteDivided_toAffine hπ data j (Nat.le_of_succ_le hj))

/-- The entire finite local contraction is unchanged over the original smooth locus. -/
theorem finiteToAffine_originalSmooth_isIso (j : ℕ) (hj : j ≤ n) :
    IsIso (finiteToAffine hπ data j hj ∣_ (chartStructure W 2).smoothLocus) := by
  induction j with
  | zero =>
    change IsIso ((𝟙 _ ≫ initialToAffine (data ⟨0, Nat.zero_lt_succ n⟩)) ∣_ _)
    rw [Category.id_comp]
    exact initialToAffine_originalSmooth_isIso hπ (data ⟨0, Nat.zero_lt_succ n⟩)
  | succ j ih =>
    have he : finiteToAffine hπ data (j + 1) hj =
        finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
          finiteToAffine hπ data j (Nat.le_of_succ_le hj) := by
      simp only [finiteToAffine, finiteContraction, Category.assoc]
    rw [he]
    exact SchemeUnchangedOpen.isIso_comp _ _ _ (finiteStep_originalSmooth_isIso hπ data j hj)
      (ih (Nat.le_of_succ_le hj))

end FLT.Mazur.WeierstrassDividedDepth
