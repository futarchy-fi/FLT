/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationPrescribedLifting
public import FLT.Mazur.FiniteRelationNamedDomainTransitions

/-!
# Prescribed boundary lifting on coherent named affine domains

The actual closed domain map and full relation square give simultaneous lifts
of lower coefficients and higher boundary values. Both values are retained on
the chosen domains, without replacing the boundary by its reduced support.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleNamedDomainBoundaryLifting
open SchemeEffectiveEpiSections FiniteRelationNamedDomainTransitions
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
variable {D A D' A' S : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  (U : A.Opens) (V : A'.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V) (hUV : V = a ⁻¹ᵁ U)
  [IsAffine S] [IsFinite p] [Etale p] (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  [IsSeparated f] (e : CategoryTheory.EquivalenceRelation p q) [IsClosedImmersion a]
  (hUa : IsAffineOpen U) (hVa : IsAffineOpen V)
set_option quotPrecheck false
local notation "r" => p.resLE U (p ⁻¹ᵁ U) le_rfl
local notation "s" => q.resLE U (p ⁻¹ᵁ U) hU.le
local notation "r'" => p'.resLE V (p' ⁻¹ᵁ V) le_rfl
local notation "s'" => q'.resLE V (p' ⁻¹ᵁ V) hV.le
local notation "c" => a.resLE U V hUV.le
variable (J : U.toScheme.IdealSheafData)
  (hJ : J.comap (p.resLE U _ le_rfl) = J.comap (q.resLE U _ hU.le))
  (I : V.toScheme.IdealSheafData) (hI : J.comap (a.resLE U V hUV.le) = I)

local instance domain_finite : IsFinite r := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- Full equivalence on the named invariant domain, sealed for coefficient specializations. -/
@[irreducible]
def domainEquivalence : CategoryTheory.EquivalenceRelation r s := by
  have Hr : IsPullback (p ⁻¹ᵁ U).ι r p U.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p U).flip
  exact EquivalenceRelationFiber.invariantRestrictionEquivalence e Hr
    (Scheme.Hom.resLE_comp_ι q hU.le).symm

omit [IsAffine S] [IsFinite p] [Etale p] [IsSeparated f] in
include hf in
/-- The restricted source map still equalizes both complete endpoints. -/
theorem domain_equalizes : r ≫ (U.ι ≫ f) = s ≫ (U.ι ≫ f) := by
  rw [← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, hf]

attribute [local irreducible] SchemeRelationInvariantSpectrum.relationPullback
  FiniteEtaleInvariantDomainCoefficients.restriction


include hf e hUa hVa hJ hI H hq in
/-- Named affine domains retain simultaneous lifting for the entire exact boundary. -/
theorem hasLifts : FiniteRelationPrescribedLifting.HasLifts r s r' s' c J hJ I hI := by
  let _ : IsAffine U.toScheme := hUa
  let _ : IsAffine V.toScheme := hVa
  let _ : IsClosedImmersion c := source_closed a U V hUV
  exact FiniteRelationPrescribedLifting.hasLifts r s r' s' c J hJ I hI
    (U.ι ≫ f) (domain_equalizes p q U hU f hf) (domainEquivalence p q U hU e)
    (arrow p p' a b H U V hUV) (arrow_isPullback p p' a b H U V hUV)
    (arrow_second p q p' q' a b H hq U V hU hV hUV)

include hf e hUa hVa hJ hI H hq in
/-- Extract both prescribed coefficient identities on the fixed named domains. -/
theorem exists_prescribed_lift (x : compatibleFunctions r' s')
    (y : compatibleFunctions (pullback.snd r J.subschemeι)
      (InvariantIdealRelation.snd J r s hJ))
    (hxy : I.subschemeι.appTop x.val =
      (IdealSheafClosedTransitions.map I J c hI).appTop y.val) :
    ∃ z : compatibleFunctions r s, (c).appTop z.val = x.val ∧
      J.subschemeι.appTop z.val = y.val := by
  have Hlift := hasLifts p q p' q' a b H hq U V hU hV hUV f hf e hUa hVa J hJ I hI
  rw [FiniteRelationPrescribedLifting.HasLifts] at Hlift
  exact Hlift x y hxy

end FLT.Mazur.FiniteEtaleNamedDomainBoundaryLifting
