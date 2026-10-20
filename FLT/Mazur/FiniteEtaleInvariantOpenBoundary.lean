/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtaleBoundarySurjectivity

/-!
# Actual boundary invariant lifts on affine invariant opens

The original relation and boundary ideal restrict to any invariant affine
source open. Finiteness of the whole relation supplies surjective restriction
on the full endpoint equalizers, without requiring the ambient source affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleInvariantOpenBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} (p q : D ⟶ A) (U : A.Opens)
  (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "r" => p.resLE U _ le_rfl
local notation "s" => q.resLE U _ hU.le
set_option quotPrecheck false
local notation "I" => J.comap U.ι
local notation "j" => (I).subschemeι

include hJ in
/-- Exact original boundary invariance survives open restriction. -/
theorem ideal_invariant : (I).comap r = (I).comap s := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hJ]

/-- The actual closed boundary map between the two full endpoint equalizers. -/
def restriction := SchemeRelationInvariantSpectrum.relationPullback r s
  (pullback.snd r j) (InvariantIdealRelation.snd I r s (ideal_invariant p q U hU J hJ))
  j (pullback.fst r j) pullback.condition
  (InvariantIdealRelation.snd_ι I r s (ideal_invariant p q U hU J hJ)).symm

variable [IsFinite p] [Etale p] [IsAffine S]
  (f : A ⟶ S) (h : p ≫ f = q ≫ f) [IsSeparated f]
  (e : CategoryTheory.EquivalenceRelation p q)

include h e in
/-- Whole-relation finiteness gives boundary lifts on every invariant affine source domain. -/
theorem restriction_surjective (ha : IsAffineOpen U) :
    Function.Surjective (restriction p q U hU J hJ) := by
  let _ : IsAffine U.toScheme := ha
  let _ : IsFinite r := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  let _ : Etale r := inferInstance
  have H : IsPullback (p ⁻¹ᵁ U).ι r p U.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p U).flip
  let er := EquivalenceRelationFiber.invariantRestrictionEquivalence e H
    (Scheme.Hom.resLE_comp_ι q hU.le).symm
  have hf : r ≫ (U.ι ≫ f) = s ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, h]
  exact AffineFiniteEtaleBoundarySurjectivity.ideal_invariant_surjective r s
    (U.ι ≫ f) hf er I (ideal_invariant p q U hU J hJ)

end FLT.Mazur.FiniteEtaleInvariantOpenBoundary
