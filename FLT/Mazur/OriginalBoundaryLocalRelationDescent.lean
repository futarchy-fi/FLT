/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonLocalClosedImage
public import FLT.Mazur.SchemeScalarComparisonNeighborhoodDescent

/-!
# Full original boundary identification and neighborhood function descent

Full original fiber coverage plus local image geometry constructs an actual
kernel identification on the canonical branch. On a smaller original image
open it also identifies regular functions with the full relation equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarComparisonNeighborhoodDescent
open SchemeScalarImageQuotient SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {D X : Scheme.{0}} [IsAffine X]
  (f : X ⟶ Spec (.of R)) (a b : D ⟶ X) (h : a ≫ f = b ≫ f)
  (U : (Spec (.of (Scalars f))).Opens)
  [Etale a] [Etale ((projection f) ∣_ U)] [IsIntegralHom ((projection f) ∣_ U)]
  [Mono (pullback.lift a b h)]

/-- Full original fiber coverage constructs a neighborhood representing compatible functions. -/
theorem exists_sectionsRingEquiv_of_local_fiber
    (z : Spec (.of (Scalars f))) (hzU : z ∈ U)
    (hz : ∀ w : (pullback f f : Scheme), (pullback.fst f f ≫ projection f) w = z →
      w ∈ Set.range (pullback.lift a b h)) :
    ∃ V : (Spec (.of (Scalars f))).Opens, V ≤ U ∧ z ∈ V ∧
      Nonempty (Γ(V.toScheme, ⊤) ≃+* compatibleFunctions (first f a b h V)
        (second f a b h V)) := by
  obtain ⟨V, hVU, hzV, hEt, hInt, hSurj⟩ :=
    SchemeScalarComparisonLocalGeometry.exists_neighborhood f a b h U z hzU hz
  let _ := hEt
  let _ := hInt
  let _ : Surjective ((pullback.lift a b h) ∣_
      ((pullback.fst f f) ⁻¹ᵁ ((projection f) ⁻¹ᵁ V))) := hSurj
  exact ⟨V, hVU, hzV, ⟨sectionsRingEquiv f a b h V⟩⟩

end FLT.Mazur.SchemeScalarComparisonNeighborhoodDescent

namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarImageQuotient SchemeScalarPrincipalNeighborhood
open SchemeScalarComparisonNeighborhoodDescent SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] originalBoundaryKernelComparison
  FlatScalarSchemeBaseChange.baseChange
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
local instance localRelationBoundaryAffine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
set_option quotPrecheck false
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "a" => pullback.snd p J.subschemeι
local notation "b" => InvariantIdealRelation.snd J p q hJ
local notation "h" => originalBoundary_scalar_condition p q J hJ
local notation "k" => originalBoundaryComparison p q J hJ
local notation "m" => originalBoundaryKernelImage p q J
variable (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
  [Etale ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]
  [IsIntegralHom ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]

include e in
/-- Full original fiber coverage identifies the entire canonical branch relation as its kernel. -/
theorem originalBoundaryComparison_isIso_of_local_fiber
    (x : PrimeSpectrum R) (y : Spec (.of (Scalars f))) (hyx : inclusion f y = x)
    (hyU : y ∈ U)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    IsIso (originalBoundaryKernelComparison p q J hJ
      (ScalarPrimeLocalizationCover.Branch x)) := by
  let _ := originalBoundaryComparison_effectiveEpi_of_local_fiber e J hJ U x y hyx hyU hy
  let _ := originalBoundaryKernelComparison_mono e J hJ (ScalarPrimeLocalizationCover.Branch x)
  exact isIso_of_mono_of_strongEpi _

attribute [local irreducible] SchemeScalarComparisonNeighborhoodDescent.first
  SchemeScalarComparisonNeighborhoodDescent.second SchemeEffectiveEpiSections.compatibleFunctions

include e in
/-- A smaller original image open represents all compatible full boundary functions. -/
theorem originalBoundary_exists_local_relation_descent
    (y : Spec (.of (Scalars f))) (hyU : y ∈ U)
    (hy : ∀ w : (pullback f f : Scheme), m w = y → w ∈ Set.range k) :
    ∃ V : (Spec (.of (Scalars f))).Opens, V ≤ U ∧ y ∈ V ∧
      Nonempty (Γ(V.toScheme, ⊤) ≃+*
        compatibleFunctions (SchemeScalarComparisonNeighborhoodDescent.first f a b h V)
          (SchemeScalarComparisonNeighborhoodDescent.second f a b h V)) := by
  let _ : Mono (pullback.lift a b h) := originalBoundaryComparison_mono e J hJ
  exact SchemeScalarComparisonNeighborhoodDescent.exists_sectionsRingEquiv_of_local_fiber
    f a b h U y hyU hy

end FLT.Mazur.EquivalenceRelationOrderedFrames
