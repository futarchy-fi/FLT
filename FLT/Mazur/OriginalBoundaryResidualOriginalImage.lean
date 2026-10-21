/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualLocalImage
public import FLT.Mazur.OriginalBoundaryFlatImageGeometry
public import FLT.Mazur.ScalarPrimeLocalizationCover

/-!
# Residual original-boundary descent from original full image geometry

The original flat closed scalar image supplies faithful flatness on every
canonical local branch. Only full relation domination is tested on the
residual intersection. Both bad closures and the whole original V(Q) remain.
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
local notation "L" => (@ScalarPrimeLocalizationCover.Branch R _)
variable [Flat (SchemeScalarImageQuotient.projection
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))]
  (hc : IsClosed (Set.range
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))
  (Q : Ideal (compatibleFunctions p q))


include e hf hc in
/-- Original full image geometry leaves only residual relation domination to prove. -/
theorem originalBoundaryLift_support_of_original_flat_image
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      Epi (originalBoundaryKernelComparison p q J hJ (L x))) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  apply originalBoundaryLift_support_of_residual_local_image e J hJ f hf t Q
  intro x hx hxQ
  exact ⟨originalBoundaryImage_faithfullyFlat p q J (L x) hc, hbranch x hx hxQ⟩

include e hf hc in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_original_flat_image
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      Epi (originalBoundaryKernelComparison p q J hJ (L x))) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_original_flat_image e J hJ f hf t hc Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
