/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAssociatedDifferentialDetection
public import FLT.Mazur.OriginalBoundaryGenericRankCoverage
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Associated affine coefficient tests for the full original comparison

Affine charts supply Noetherian coordinates on every locally Noetherian test.
Rigidity is tested only at their associated primes, retaining embedded points.
Generic coverage on the actual full rank stages supplies the point-coverage
input. No Noetherianity of global sections or compactness of the test is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_affine_tests {C T B : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T)
    (h : ∀ i, RingHom.ker c.appTop.hom ≤
      RingHom.ker (B.affineCover.f i ≫ t).appTop.hom) :
    RingHom.ker c.appTop.hom ≤ RingHom.ker t.appTop.hom := by
  intro r hr
  change t.appTop r = 0
  apply (SchemeEffectiveEpiSections.functionEquiv B).symm.injective
  apply B.affineCover.hom_ext
  intro i
  apply (SchemeEffectiveEpiSections.functionEquiv (B.affineCover.X i)).injective
  have he : (B.affineCover.f i ≫ t).appTop r = 0 := h i hr
  simpa only [SchemeEffectiveEpiSections.functionEquiv_comp, Equiv.apply_symm_apply,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, map_zero] using he

private theorem affine_test_coverage {C T B U : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T) (v : U ⟶ B) (h : Set.range t ⊆ Set.range c) :
    Set.range (v ≫ t) ⊆ Set.range c := by
  rintro _ ⟨u, rfl⟩
  exact h (Set.mem_range_self (v u))

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance associatedChartBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism

local instance associatedChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance associatedChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance associatedChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "x" => pullback.fst f f ≫ J.subschemeι

include e

/-- Associated primes on actual affine charts suffice for every full nonreduced equation. -/
theorem originalBoundary_kernel_of_affine_associated_unramified
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hU : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      ∀ i, ∀ P : PrimeSpectrum Γ(B.affineCover.X i, ⊤),
        P.asIdeal ∈ associatedPrimes Γ(B.affineCover.X i, ⊤) Γ(B.affineCover.X i, ⊤) →
        PrimeSpectrum.comap ((B.affineCover.f i ≫ t) ≫ pullback.snd f f).appTop.hom P ∈
          Algebra.unramifiedLocus (Scalars f) Γ(J.subscheme, ⊤)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  apply kernel_le_of_affine_tests c t
  intro i
  let _ : IsAffine (B.affineCover.X i) := isAffine_Spec _
  let _ := isLocallyNoetherian_of_isOpenImmersion (B.affineCover.f i)
  let _ := IsLocallyNoetherian.component_noetherian
    (⟨⊤, isAffineOpen_top (B.affineCover.X i)⟩ : (B.affineCover.X i).affineOpens)
  exact originalBoundary_kernel_of_associated_unramified e J hJ
    (B.affineCover.f i ≫ t) (affine_test_coverage c t _ h) hft (hU i)

/-- Actual generic rank coverage and associated affine rigidity detect the entire kernel. -/
theorem originalBoundary_kernel_of_generic_ranks_affine_associated
    (t : B ⟶ pullback f f) (k : ℕ)
    (h : ∀ n, genericPoints (rankPullbackThickening (Over.mk p) (t ≫ x) n k) ⊆
      (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hU : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      ∀ i, ∀ P : PrimeSpectrum Γ(B.affineCover.X i, ⊤),
        P.asIdeal ∈ associatedPrimes Γ(B.affineCover.X i, ⊤) Γ(B.affineCover.X i, ⊤) →
        PrimeSpectrum.comap ((B.affineCover.f i ≫ t) ≫ pullback.snd f f).appTop.hom P ∈
          Algebra.unramifiedLocus (Scalars f) Γ(J.subscheme, ⊤)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  originalBoundary_kernel_of_affine_associated_unramified e J hJ t
    (originalBoundary_coverage_of_generic_rankStages J hJ t k h) hft hU

end FLT.Mazur.EquivalenceRelationOrderedFrames
