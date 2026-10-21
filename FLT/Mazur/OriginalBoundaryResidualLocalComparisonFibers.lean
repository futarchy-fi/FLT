/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonLocalClosedImage
public import FLT.Mazur.OriginalBoundaryResidualLocalImage

/-!
# Residual original powers from full fibers and local image geometry

The local closed-obstruction construction replaces assumed neighborhood
comparison coverage by coverage of the full original fiber. Both bad
closures, the whole exceptional zero locus and explicit finite generation
are retained; the frontier geometry and fiber coverage remain inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] originalBoundaryKernelComparison
  FlatScalarSchemeBaseChange.baseChange
variable {D A Z : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine Z] (f : A ⟶ Z) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => scalarMorphism (Subring.subtype (compatibleFunctions p q))
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "b₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
variable (Q : Ideal (compatibleFunctions p q))

include e in
omit [IsSeparated p] [QuasiCompact p] in
private theorem branch_of_local_comparison_fiber
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hx : x ∈ closure (σ '' (J.support : Set A)))
    (hgeo : ∀ y : Spec (.of (Scalars b₀)), inclusion b₀ y = x →
      ∃ U : (Spec (.of (Scalars b₀))).Opens, y ∈ U ∧
        Etale ((projection b₀) ∣_ U) ∧ IsIntegralHom ((projection b₀) ∣_ U) ∧
          (∀ w : (pullback b₀ b₀ : Scheme), originalBoundaryKernelImage p q J w = y →
            w ∈ Set.range (originalBoundaryComparison p q J hJ))) :
    (RingHom.kerLift (FlatScalarFunctionPushout.scalarMap
      (base R (ScalarPrimeLocalizationCover.Branch x) J.subscheme))).FaithfullyFlat ∧
      Epi (originalBoundaryKernelComparison p q J hJ
        (ScalarPrimeLocalizationCover.Branch x)) := by
  apply (originalBoundary_existsUnique_image_point p q J x hx).exists.elim
  intro y hyx
  apply (hgeo y hyx).elim
  intro U hU
  let _ := hU.2.1
  let _ := hU.2.2.1
  let _ := originalBoundaryComparison_effectiveEpi_of_local_fiber e J hJ U x y hyx
    hU.1 hU.2.2.2
  exact ⟨originalBoundary_image_faithfullyFlat_of_integral_neighborhood
    p q J x y hyx U hU.1, inferInstance⟩

include e hf in
/-- Full fiber coverage and local image geometry construct residual original branch descent. -/
theorem originalBoundaryLift_support_of_local_comparison_fibers
    (hgeo : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (σ '' (J.support : Set A)) ∩
        closure (σ '' (finiteTargetOpen p : Set A)ᶜ) →
      x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      ∀ y : Spec (.of (Scalars b₀)), inclusion b₀ y = x →
        ∃ U : (Spec (.of (Scalars b₀))).Opens, y ∈ U ∧
          Etale ((projection b₀) ∣_ U) ∧ IsIntegralHom ((projection b₀) ∣_ U) ∧
          (∀ w : (pullback b₀ b₀ : Scheme), originalBoundaryKernelImage p q J w = y →
            w ∈ Set.range (originalBoundaryComparison p q J hJ))) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  apply originalBoundaryLift_support_of_residual_local_image e J hJ f hf t Q
  intro x hx hxQ
  exact branch_of_local_comparison_fiber e J hJ x hx.1 (hgeo x hx hxQ)

include e hf in
/-- Explicit finite generation turns local fiber geometry into uniform original powers. -/
theorem exists_pow_le_originalBoundaryLiftIdeal_of_local_comparison_fibers
    (hgeo : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (σ '' (J.support : Set A)) ∩
        closure (σ '' (finiteTargetOpen p : Set A)ᶜ) →
      x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      ∀ y : Spec (.of (Scalars b₀)), inclusion b₀ y = x →
        ∃ U : (Spec (.of (Scalars b₀))).Opens, y ∈ U ∧
          Etale ((projection b₀) ∣_ U) ∧ IsIntegralHom ((projection b₀) ∣_ U) ∧
          (∀ w : (pullback b₀ b₀ : Scheme), originalBoundaryKernelImage p q J w = y →
            w ∈ Set.range (originalBoundaryComparison p q J hJ)))
    (hfg : Q.FG) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J t.val := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      (originalBoundaryLift_support_of_local_comparison_fibers e J hJ f hf t Q hgeo)) hfg

end FLT.Mazur.EquivalenceRelationOrderedFrames
