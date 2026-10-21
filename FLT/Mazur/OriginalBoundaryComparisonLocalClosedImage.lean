/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonClosedImage
public import FLT.Mazur.SchemeScalarComparisonLocalGeometry

/-!
# Original boundary domination from local image geometry and full fiber coverage

The actual boundary equivalence relation supplies comparison monicity.
Etale integral geometry is needed only near the original image point; full
fiber coverage then constructs a smaller neighborhood and branch domination.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarImageQuotient SchemeScalarPrincipalNeighborhood
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
variable [Etale p]
  (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
  [Etale ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]
  [IsIntegralHom ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]

include e in
/-- Actual full fiber coverage shrinks local image geometry to a full comparison neighborhood. -/
theorem originalBoundaryComparison_neighborhood_of_local_fiber
    (y : Spec (.of (Scalars f))) (hyU : y ∈ U)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    ∃ V : (Spec (.of (Scalars f))).Opens, V ≤ U ∧ y ∈ V ∧
      Etale ((projection f) ∣_ V) ∧ IsIntegralHom ((projection f) ∣_ V) ∧
        Surjective (k ∣_ (m ⁻¹ᵁ V)) := by
  let _ : Mono (pullback.lift (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ) (originalBoundary_scalar_condition p q J hJ)) :=
    originalBoundaryComparison_mono e J hJ
  exact SchemeScalarComparisonLocalGeometry.exists_neighborhood f
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)
    (originalBoundary_scalar_condition p q J hJ) U y hyU hy

include e in
/-- Local geometry and a full fiber give effective domination on the canonical scalar branch. -/
theorem originalBoundaryComparison_effectiveEpi_of_local_fiber [IsAffine A]
    (x : PrimeSpectrum R) (y : Spec (.of (Scalars f))) (hyx : inclusion f y = x)
    (hyU : y ∈ U)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    EffectiveEpi (originalBoundaryKernelComparison p q J hJ
      (ScalarPrimeLocalizationCover.Branch x)) := by
  obtain ⟨V, _, hyV, hEt, _, hSurj⟩ :=
    originalBoundaryComparison_neighborhood_of_local_fiber e J hJ U y hyU hy
  let _ := hEt
  let _ := hSurj
  exact originalBoundaryComparison_effectiveEpi_of_neighborhood p q J hJ x y hyx V hyV

include e in
/-- The same local fiber data constructs faithful flat coefficients and full domination together. -/
theorem originalBoundaryComparison_descent_of_local_fiber [IsAffine A]
    (x : PrimeSpectrum R) (y : Spec (.of (Scalars f))) (hyx : inclusion f y = x)
    (hyU : y ∈ U)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    (RingHom.kerLift (FlatScalarFunctionPushout.scalarMap
      (FlatScalarSchemeBaseChange.base R (ScalarPrimeLocalizationCover.Branch x)
        J.subscheme))).FaithfullyFlat ∧
      EffectiveEpi (originalBoundaryKernelComparison p q J hJ
        (ScalarPrimeLocalizationCover.Branch x)) :=
  ⟨originalBoundary_image_faithfullyFlat_of_integral_neighborhood p q J x y hyx U hyU,
    originalBoundaryComparison_effectiveEpi_of_local_fiber e J hJ U x y hyx hyU hy⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
