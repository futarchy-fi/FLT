/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationPrincipalHomogeneousCorrections
public import FLT.Mazur.RankStageCoreBoundaryCoefficients

/-!
# Constructed homogeneous corrections inside the actual affine rank cores

At every fixed rank and order, independent principal-patch boundary lifts
on a whole core have exact homogeneous corrections. The boundary is the
full pullback of the original ideal. No reduction or fiberwise replacement
enters the construction. Compatibility between orders and between distinct
ambient cores still requires a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples InvariantOpenCoefficientRestriction SchemeEffectiveEpiSections
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance principalCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance principalCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance principalCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (k : ℕ)
local notation "C" => rankStageCore e n a ha k
local notation "X" => (C).toScheme
local notation "hC" => rankStageCore_invariant e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE C _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE C _ (hC).le
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "i" => (I).subschemeι
attribute [local irreducible] rankStageCore rankStageFirst rankStageSecond

variable {ι : Type*} [Finite ι] (b : ι → rankStageCoreInvariants e n a ha k)
local notation "U" j => (X).basicOpen (b j).val
local notation "hU" j => compatibleFunctions_basicOpen r s (b j)

/-- Full principal patches of each actual affine core have constructed homogeneous corrections. -/
theorem exists_rankStage_principal_core_corrections (hb : (⨆ j, U j) = ⊤)
    (v : ∀ j, coefficients r s (U j) (hU j)) (t : Γ((I).subscheme, ⊤))
    (hv : ∀ j, (principalPullbackMap i (b j).val).appTop (v j).val =
      ((I).subscheme.basicOpen ((i).appTop (b j).val)).ι.appTop t) :
    ∃ c : ∀ j, coefficients r s (U j) (hU j),
      (∀ j, (principalPullbackMap i (b j).val).appTop (c j).val = 0) ∧
      ∀ j l,
        ((X).homOfLE (inf_le_left : (U j) ⊓ (U l) ≤ (U j))).appTop (v j - c j).val =
          ((X).homOfLE (inf_le_right : (U j) ⊓ (U l) ≤ (U l))).appTop (v l - c l).val := by
  let _ := rankStageFirst_finite (p := p) n k
  let _ : IsAffine X := rankStageCore_affine e n a ha k
  let _ : IsAffine (I).subscheme := isAffine_of_isAffineHom (I).subschemeι
  let _ : IsFinite r := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  let _ : IsAffine ((rankStageFirst (p := p) n k) ⁻¹ᵁ C).toScheme :=
    isAffine_of_isAffineHom r
  have H : IsPullback ((rankStageFirst (p := p) n k) ⁻¹ᵁ C).ι r
      (rankStageFirst (p := p) n k) (C).ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict _ _).flip
  let er := EquivalenceRelationFiber.invariantRestrictionEquivalence
    (rankStageEquivalence e n k) H (Scheme.Hom.resLE_comp_ι _ (hC).le).symm
  exact FiniteRelationPrincipalBoundaryCover.exists_homogeneous_corrections
    r s er b i hb v t hv

end FLT.Mazur.EquivalenceRelationOrderedFrames
