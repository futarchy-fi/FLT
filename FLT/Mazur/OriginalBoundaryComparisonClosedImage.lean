/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonNeighborhood
public import FLT.Mazur.OriginalBoundaryScalarMonomorphism
public import FLT.Mazur.SchemeScalarImageKernelGeometry

/-!
# Closed full-comparison obstructions on the original boundary image

The actual boundary equivalence relation makes the original comparison monic.
Etale integral exact-image geometry closes its entire missed image. Coverage
of one full image fiber therefore constructs a neighborhood and effective
domination on the canonical scalar branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarImageQuotient SchemeScalarPrincipalNeighborhood
open SchemeComparisonCoverageLocus
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "k" => originalBoundaryComparison p q J hJ
local notation "m" => originalBoundaryKernelImage p q J

include e in
/-- The actual boundary equivalence relation makes the unchanged original comparison monic. -/
theorem originalBoundaryComparison_mono : Mono k := by
  let _ : JointlyMono₂ p q := e.toJointlyMono₂
  constructor
  intro Y a b hab
  apply JointlyMono₂.right_cancellation (p₁ := pullback.snd p J.subschemeι)
    (p₂ := InvariantIdealRelation.snd J p q hJ)
  · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_fst] using
      congrArg (fun w ↦ w ≫ pullback.fst f f) hab
  · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_snd] using
      congrArg (fun w ↦ w ≫ pullback.snd f f) hab

variable [Etale p]
  [Etale (projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))]
  [IsIntegralHom (projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))]

include e in
/-- The full missed original comparison image is closed under etale integral image geometry. -/
theorem originalBoundaryComparison_missedImage_isClosed : IsClosed (m '' (Set.range k)ᶜ) := by
  let _ : Mono (pullback.lift (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ) (originalBoundary_scalar_condition p q J hJ)) :=
    originalBoundaryComparison_mono e J hJ
  exact SchemeScalarImageKernelGeometry.comparison_missedImage_isClosed f
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)
    (originalBoundary_scalar_condition p q J hJ)

include e in
/-- Full original fiber coverage constructs a comparison neighborhood on the exact image. -/
theorem originalBoundaryComparison_neighborhood_of_fiber
    (y : Spec (.of (Scalars f)))
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    ∃ U : (Spec (.of (Scalars f))).Opens, y ∈ U ∧ Surjective (k ∣_ (m ⁻¹ᵁ U)) :=
  exists_neighborhood_of_fiber_coverage k m
    (originalBoundaryComparison_missedImage_isClosed e J hJ) y hy

include e in
/-- Full fiber coverage, rather than an assumed neighborhood cover, supplies branch domination. -/
theorem originalBoundaryComparison_effectiveEpi_of_fiber [IsAffine A]
    (x : PrimeSpectrum R) (y : Spec (.of (Scalars f))) (hyx : inclusion f y = x)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    EffectiveEpi (originalBoundaryKernelComparison p q J hJ
      (ScalarPrimeLocalizationCover.Branch x)) := by
  obtain ⟨U, hyU, hU⟩ := originalBoundaryComparison_neighborhood_of_fiber e J hJ y hy
  let _ := hU
  exact originalBoundaryComparison_effectiveEpi_of_neighborhood p q J hJ x y hyx U hyU

end FLT.Mazur.EquivalenceRelationOrderedFrames
