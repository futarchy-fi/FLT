/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtaleFullBoundaryCoefficients
public import FLT.Mazur.FiniteEtaleInvariantOpenBoundary
public import FLT.Mazur.InvariantIdealRelationCoefficientMembership
public import FLT.Mazur.InvariantOpenCoefficientRestriction

/-!
# Original boundary lifts where the restricted relation is finite

Finiteness is needed only over the invariant affine open, not on the entire
original source. Pull back the original full boundary invariant and lift it
through the entire restricted relation, retaining its literal boundary value.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.InvariantAffineFiniteBoundaryLift
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} (p q : D ⟶ A) [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (U : A.Opens)
  (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (ha : IsAffineOpen U)
  [IsFinite (p.resLE U _ le_rfl)]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "r" => p.resLE U _ le_rfl
local notation "s" => q.resLE U _ hU.le
local notation "I" => Scheme.IdealSheafData.comap J (Scheme.Opens.ι U)

include e ha hf in
/-- A finite restricted original relation constructs an exact lift of the full original boundary. -/
theorem exists_lift
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ u : coefficients p q U hU, (I).subschemeι.appTop u.val =
      (IdealSheafClosedTransitions.map I J U.ι rfl).appTop t.val := by
  let _ : IsAffine U.toScheme := ha
  have H : IsPullback (p ⁻¹ᵁ U).ι r p U.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p U).flip
  have hq : (p ⁻¹ᵁ U).ι ≫ q = s ≫ U.ι := (Scheme.Hom.resLE_comp_ι q hU.le).symm
  let er := EquivalenceRelationFiber.invariantRestrictionEquivalence e H hq
  have hI := FiniteEtaleInvariantOpenBoundary.ideal_invariant p q U hU J hJ
  let y : compatibleFunctions (pullback.snd r (I).subschemeι)
      (InvariantIdealRelation.snd I r s hI) :=
    ⟨(IdealSheafClosedTransitions.map I J U.ι rfl).appTop t.val,
      InvariantIdealRelationCoefficients.pullback_mem p q r s U.ι (p ⁻¹ᵁ U).ι
        H.w hq J hJ I hI rfl t⟩
  have he : r ≫ (U.ι ≫ f) = s ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, hf]
  exact AffineFiniteEtaleFullBoundaryCoefficients.exists_initial_lift r s (U.ι ≫ f)
    he er I hI y

end FLT.Mazur.InvariantAffineFiniteBoundaryLift
