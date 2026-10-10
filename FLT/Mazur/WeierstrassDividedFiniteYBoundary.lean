/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorYBoundary
public import FLT.Mazur.WeierstrassGlobalModificationGluing
public import FLT.Mazur.SchemeUnchangedOpenLift
public import FLT.Mazur.SchemeUnchangedOpenComposition

/-!
# The complete original Y-boundary through finite divided iteration

Every actual finite contraction is an isomorphism over the original D(y).
Its inverse gives the original overlap as an actual open immersion into the
finite local model, with the entire inverse image retained.
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
/-- The full original D(y) is unchanged under the initial actual affine contraction. -/
theorem initialToAffine_originalY_isIso :
    IsIso (initialToAffine d ∣_ PrimeSpectrum.basicOpen (coord W 2 1)) := by
  have H := WeierstrassModificationReesCoordinates.originalOpen_isPullback W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
    (coord W 2 1) (Ideal.subset_span (by simp))
  apply SchemeUnchangedOpen.isIso_precomp (initialExteriorIso d)
  exact SchemeUnchangedOpen.isIso_of_identity_pullback_eq _ _ _ H _
    (TopologicalSpace.Opens.ext (PrincipalAffineRefinement.range_inclusion _))

variable {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))

omit [IsBezout R] in
/-- Each actual local finite step is unchanged over the previous original-boundary preimage. -/
theorem finiteStep_originalY_isIso (j : ℕ) (hj : j + 1 ≤ n) :
    IsIso (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ∣_
      finiteToAffine hπ data j (Nat.le_of_succ_le hj) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (coord W 2 1)) :=
  Exterior.step_originalY_isIso hπ _ _ _
    (finiteDivided_toAffine hπ data j (Nat.le_of_succ_le hj))

/-- Every actual finite affine contraction is unchanged over the entire original D(y). -/
theorem finiteToAffine_originalY_isIso (j : ℕ) (hj : j ≤ n) :
    IsIso (finiteToAffine hπ data j hj ∣_ PrimeSpectrum.basicOpen (coord W 2 1)) := by
  induction j with
  | zero =>
    change IsIso ((𝟙 _ ≫ initialToAffine (data ⟨0, Nat.zero_lt_succ n⟩)) ∣_ _)
    rw [Category.id_comp]
    exact initialToAffine_originalY_isIso hπ (data ⟨0, Nat.zero_lt_succ n⟩)
  | succ j ih =>
    have he : finiteToAffine hπ data (j + 1) hj =
        finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
          finiteToAffine hπ data j (Nat.le_of_succ_le hj) := by
      simp only [finiteToAffine, finiteContraction, Category.assoc]
    rw [he]
    exact SchemeUnchangedOpen.isIso_comp _ _ _ (finiteStep_originalY_isIso hπ data j hj)
      (ih (Nat.le_of_succ_le hj))

/-- The original affine Y-boundary included in the actual finite local model. -/
def finiteYBoundary (j : ℕ) (hj : j ≤ n) :
    overlapScheme W 2 1 ⟶ finiteModification hπ data j hj :=
  SchemeUnchangedOpen.lift (finiteToAffine hπ data j hj) (overlapInclusion W 2 1) (by
    have he : (overlapInclusion W 2 1).opensRange = PrimeSpectrum.basicOpen (coord W 2 1) :=
      TopologicalSpace.Opens.ext (PrincipalAffineRefinement.range_inclusion _)
    rw [he]
    exact finiteToAffine_originalY_isIso hπ data j hj)

instance finiteYBoundary_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteYBoundary hπ data j hj) := by
  unfold finiteYBoundary
  infer_instance

/-- The finite boundary retains the exact original affine-cubic overlap inclusion. -/
@[reassoc] theorem finiteYBoundary_contraction (j : ℕ) (hj : j ≤ n) :
    finiteYBoundary hπ data j hj ≫ finiteToAffine hπ data j hj = overlapInclusion W 2 1 :=
  SchemeUnchangedOpen.lift_comp _ _ _

/-- The original boundary is the entire pullback under the finite local contraction. -/
theorem finiteYBoundary_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (𝟙 _) (finiteYBoundary hπ data j hj)
      (overlapInclusion W 2 1) (finiteToAffine hπ data j hj) :=
  SchemeUnchangedOpen.lift_isPullback _ _ _

/-- No extra points occur above the original Y-boundary at any finite depth. -/
theorem finiteYBoundary_preimage (j : ℕ) (hj : j ≤ n) :
    finiteToAffine hπ data j hj ⁻¹' Set.range (overlapInclusion W 2 1) =
      Set.range (finiteYBoundary hπ data j hj) :=
  SchemeUnchangedOpen.lift_preimage _ _ _

end FLT.Mazur.WeierstrassDividedDepth
