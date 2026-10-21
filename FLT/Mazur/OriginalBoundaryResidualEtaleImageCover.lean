/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryEtaleImageLift
public import FLT.Mazur.OriginalBoundaryResidualScalarCover

/-!
# Residual coverage by etale full scalar images

All quotient maps and full relation comparisons are fixed constructions.
Coverage needs an etale surjective full image projection and a surjective
canonical kernel comparison, independently of the section t.
Both bad image closures and the whole original V(Q) remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Z : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine Z] (f : A ⟶ Z) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => Subring.subtype (compatibleFunctions p q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable {ι : Type*} (S : ι → Type) [∀ i, CommRing (S i)]
  [∀ i, Algebra (invariants p.appTop.hom q.appTop.hom) (S i)]
  [∀ i, Module.Flat (invariants p.appTop.hom q.appTop.hom) (S i)]
  (Q : Ideal (compatibleFunctions p q))


include e hf in
/-- Full image geometry constructs the required original residual multipliers. -/
theorem originalBoundaryLift_support_of_residual_etale_image_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      Etale (SchemeScalarImageQuotient.projection (base R (S i) J.subscheme)) ∧
      Surjective (SchemeScalarImageQuotient.projection (base R (S i) J.subscheme)) ∧
      Surjective (originalBoundaryKernelComparison p q J hJ (S i))) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  apply originalBoundaryLift_support_of_residual_scalar_cover e J hJ f hf t S Q
  intro x hx hxQ
  obtain ⟨i, P, hP, he, hc, hk⟩ := hbranch x hx hxQ
  let _ := he
  let _ := hc
  let _ := hk
  obtain ⟨s, hs⟩ := originalBoundary_scalar_of_etale_image p q J hJ (S i) t
  exact ⟨i, P, s, hP, hs⟩

include e hf in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_etale_image_cover
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
    ∃ (i : ι) (P : PrimeSpectrum (S i)),
      P.asIdeal.comap (algebraMap (invariants p.appTop.hom q.appTop.hom) (S i)) = x.asIdeal ∧
      Etale (SchemeScalarImageQuotient.projection (base R (S i) J.subscheme)) ∧
      Surjective (SchemeScalarImageQuotient.projection (base R (S i) J.subscheme)) ∧
      Surjective (originalBoundaryKernelComparison p q J hJ (S i))) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_residual_etale_image_cover e J hJ f hf t S Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
