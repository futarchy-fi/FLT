/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleNamedDomainBoundaryLifting

/-!
# Initial full boundary coefficient lifts on named affine domains

The exact invariant ideal may be specified on the named domain itself.
Extract an invariant lift with its literal full boundary coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleNamedBoundaryCoefficients
open SchemeEffectiveEpiSections FiniteEtaleNamedDomainBoundaryLifting
set_option backward.isDefEq.respectTransparency true
variable {D A S : Scheme.{0}} (p q : D ⟶ A) (U : A.Opens)
  (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) [IsAffine S] [IsFinite p] [Etale p]
  (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (e : CategoryTheory.EquivalenceRelation p q) (hUa : IsAffineOpen U)
  (J : U.toScheme.IdealSheafData)
  (hJ : J.comap (p.resLE U _ le_rfl) = J.comap (q.resLE U _ hU.le))
local notation "r" => p.resLE U _ le_rfl
local notation "s" => q.resLE U _ hU.le

include hf e hUa in
/-- Every invariant of the full named boundary lifts to the entire named relation. -/
theorem exists_lift (y : compatibleFunctions (pullback.snd r J.subschemeι)
    (InvariantIdealRelation.snd J r s hJ)) :
    ∃ z : compatibleFunctions r s, J.subschemeι.appTop z.val = y.val := by
  let _ : IsAffine U.toScheme := hUa
  let _ : IsFinite r := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  obtain ⟨z, hz⟩ := AffineFiniteEtaleBoundarySurjectivity.ideal_invariant_surjective
    r s (U.ι ≫ f) (domain_equalizes p q U hU f hf) (domainEquivalence p q U hU e) J hJ y
  exact ⟨z, congrArg Subtype.val hz⟩

end FLT.Mazur.FiniteEtaleNamedBoundaryCoefficients
