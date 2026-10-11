/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOriginalXOpen
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.RegularPrincipalOpenLiftExt
public import FLT.Mazur.WeierstrassGlobalModificationGluing
public import FLT.Mazur.SchemeUnchangedOpenLift
public import FLT.Mazur.SchemeUnchangedOpenComposition

/-!
# The complete original X-open through finite divided iteration

Every actual finite contraction is an isomorphism over the original D(x).
Its inverse gives the original overlap as an actual open immersion into the
finite local model, with the entire inverse image retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ} (d : Data W π k)
open WeierstrassIntegralChart

include hπ in
/-- The full original D(x) is unchanged under the initial actual affine contraction. -/
theorem initialToAffine_originalX_isIso :
    IsIso (initialToAffine d ∣_ PrimeSpectrum.basicOpen (coord W 2 0)) := by
  have H := WeierstrassModificationReesCoordinates.originalOpen_isPullback W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
    (coord W 2 0) (Ideal.subset_span (by simp))
  apply SchemeUnchangedOpen.isIso_precomp (initialExteriorIso d)
  exact SchemeUnchangedOpen.isIso_of_identity_pullback_eq _ _ _ H _
    (TopologicalSpace.Opens.ext (PrincipalAffineRefinement.range_inclusion _))

variable {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))

omit [IsBezout R] in
/-- Each actual local finite step is unchanged over the previous original-boundary preimage. -/
theorem finiteStep_originalX_isIso (j : ℕ) (hj : j + 1 ≤ n) :
    IsIso (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ∣_
      finiteToAffine hπ data j (Nat.le_of_succ_le hj) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (coord W 2 0)) :=
  Exterior.step_originalX_isIso hπ _ _ _ _
    (finiteDivided_toAffine hπ data j (Nat.le_of_succ_le hj))

/-- Every actual finite affine contraction is unchanged over the entire original D(x). -/
theorem finiteToAffine_originalX_isIso (j : ℕ) (hj : j ≤ n) :
    IsIso (finiteToAffine hπ data j hj ∣_ PrimeSpectrum.basicOpen (coord W 2 0)) := by
  induction j with
  | zero =>
    change IsIso ((𝟙 _ ≫ initialToAffine (data ⟨0, Nat.zero_lt_succ n⟩)) ∣_ _)
    rw [Category.id_comp]
    exact initialToAffine_originalX_isIso hπ (data ⟨0, Nat.zero_lt_succ n⟩)
  | succ j ih =>
    have he : finiteToAffine hπ data (j + 1) hj =
        finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
          finiteToAffine hπ data j (Nat.le_of_succ_le hj) := by
      simp only [finiteToAffine, finiteContraction, Category.assoc]
    rw [he]
    exact SchemeUnchangedOpen.isIso_comp _ _ _ (finiteStep_originalX_isIso hπ data j hj)
      (ih (Nat.le_of_succ_le hj))

/-- The original horizontal principal open in the actual finite local model. -/
def finiteOriginalXOpen (j : ℕ) (hj : j ≤ n) :=
  SchemeUnchangedOpen.lift (finiteToAffine hπ data j hj)
    (PrincipalAffineRefinement.inclusion (coord W 2 0)) (by
      have he : (PrincipalAffineRefinement.inclusion (coord W 2 0)).opensRange =
          PrimeSpectrum.basicOpen (coord W 2 0) :=
        TopologicalSpace.Opens.ext (PrincipalAffineRefinement.range_inclusion _)
      rw [he]
      exact finiteToAffine_originalX_isIso hπ data j hj)

/-- The horizontal open retains the full original cubic contraction. -/
theorem finiteOriginalXOpen_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (𝟙 _) (finiteOriginalXOpen hπ data j hj ≫ finiteLocalChart hπ data j hj)
      (PrincipalAffineRefinement.inclusion (coord W 2 0) ≫ integralCurveChart W 2)
      (finiteGlobalContraction hπ data j hj) := by
  have H : IsPullback (𝟙 _) (finiteOriginalXOpen hπ data j hj)
      (PrincipalAffineRefinement.inclusion (coord W 2 0))
      (finiteToAffine hπ data j hj) := SchemeUnchangedOpen.lift_isPullback _ _ _
  exact H.paste_vert (finiteLocal_isPullback hπ data j hj)

/-- A regular original horizontal coordinate detects arbitrary whole-model lifts. -/
theorem finiteGlobalContraction_ext_of_regular_x (j : ℕ) (hj : j ≤ n)
    {S : Type u} [CommRing S] (φ : Coordinate W 2 →+* S)
    (hx : IsRegular (φ (coord W 2 0)))
    (f g : Spec (.of S) ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2)
    (hg : g ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2) : f = g := by
  let _ := finiteGlobalContraction_isProper hπ data j hj
  exact RegularPrincipalOpen.lift_ext (finiteGlobalContraction hπ data j hj)
    (integralCurveChart W 2) (coord W 2 0) _
    (finiteOriginalXOpen_isPullback hπ data j hj) φ hx f g hf hg

end FLT.Mazur.WeierstrassDividedDepth
