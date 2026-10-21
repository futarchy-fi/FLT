/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualEtaleImageCover
public import FLT.Mazur.SchemeScalarImageGeometry
public import FLT.Mazur.ScalarPrimeLocalizationCover

/-!
# Original residual coverage by closed etale local images

Every original prime has a constructed flat localization and a maximal ideal
above it. Closedness of
the full branch image supplies image-projection surjectivity. Only etaleness
and coverage of the fixed full relation comparison remain geometric inputs.
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
variable (Q : Ideal (compatibleFunctions p q))


include e hf in
/-- Full image geometry constructs the required original residual multipliers. -/
theorem originalBoundaryLift_support_of_residual_local_etale_image
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      Etale (SchemeScalarImageQuotient.projection (base R (L x) J.subscheme)) ∧
      IsClosed (Set.range (base R (L x) J.subscheme)) ∧
      Surjective (originalBoundaryKernelComparison p q J hJ (L x))) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  apply originalBoundaryLift_support_of_residual_etale_image_cover e J hJ f hf t
    (fun x : PrimeSpectrum (compatibleFunctions p q) ↦ L x) Q
  intro x hx hxQ
  obtain ⟨he, hc, hk⟩ := hbranch x hx hxQ
  let _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  let _ : IsAffine (baseChange R (L x) J.subscheme) := by
    unfold baseChange
    infer_instance
  exact ⟨x, @ScalarPrimeLocalizationCover.point R _ x,
    @ScalarPrimeLocalizationCover.point_comap R _ x, he,
    SchemeScalarImageQuotient.projection_surjective_of_isClosed_range _ hc, hk⟩

include e hf in
/-- Finite generation of the specified ideal alone gives one power of original lift multipliers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_local_etale_image
  (hbranch : ∀ x : PrimeSpectrum (compatibleFunctions p q),
    x ∈ closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (J.support : Set A)) ∩
      closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
       (finiteTargetOpen p : Set A)ᶜ) →
    x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      Etale (SchemeScalarImageQuotient.projection (base R (L x) J.subscheme)) ∧
      IsClosed (Set.range (base R (L x) J.subscheme)) ∧
      Surjective (originalBoundaryKernelComparison p q J hJ (L x))) (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_residual_local_etale_image e J hJ f hf t Q hbranch)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
