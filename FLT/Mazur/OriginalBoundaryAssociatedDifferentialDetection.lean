/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AssociatedPrimePowerDetection
public import FLT.Mazur.OriginalBoundaryDifferentialKernelSupport

/-!
# Full original equations from rigidity at associated coefficient primes

Only the associated primes of the test coordinates must avoid the pulled-back
support of scalar differentials. This includes embedded primes and detects
nilpotent equations. Neither a unit denominator nor rigidity at every point
is required. Actual comparison-image coverage remains a geometric input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_associated_denominators
    {R S T U : Type} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [IsNoetherianRing T] (u : R →+* S) (v : R →+* T) (w : U →+* T) (I : Ideal U)
    (hp : ∀ a ∈ I, ∀ r, u r = 0 → ∃ k : ℕ, w a ^ k * v r = 0)
    (ha : ∀ P ∈ associatedPrimes T T, ∃ a ∈ I, w a ∉ P) :
    RingHom.ker u ≤ RingHom.ker v := by
  intro r hr
  apply AssociatedPrimePowerDetection.eq_zero_of_associated_powers (R := T)
  intro P hP
  obtain ⟨a, ha, hPa⟩ := ha P hP
  exact ⟨w a, hPa, hp a ha r hr⟩

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance associatedDifferentialBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism

include e

variable [CompactSpace B] [IsNoetherianRing Γ(B, ⊤)]

/-- Differential support may meet the test, provided it avoids every associated prime. -/
theorem originalBoundary_kernel_of_associated_differential_annihilators
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (hA : ∀ P ∈ associatedPrimes Γ(B, ⊤) Γ(B, ⊤),
      ∃ a : Γ(J.subscheme, ⊤),
        (let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra;
          a ∈ Module.annihilator Γ(J.subscheme, ⊤)
            (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) ∧
        (t ≫ pullback.snd f f).appTop a ∉ P) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply kernel_le_of_associated_denominators (c).appTop.hom t.appTop.hom
    (t ≫ pullback.snd f f).appTop.hom
    (Module.annihilator Γ(J.subscheme, ⊤)
      (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) _ hA
  intro a ha r hr
  exact originalBoundary_differential_power_kernel e J hJ t h a ha r hr

/-- Essential finite type constructs the needed annihilators at the associated test primes. -/
theorem originalBoundary_kernel_of_associated_unramified
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (hft : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      Algebra.EssFiniteType (Scalars f) Γ(J.subscheme, ⊤))
    (hU : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      ∀ P : PrimeSpectrum Γ(B, ⊤),
        P.asIdeal ∈ associatedPrimes Γ(B, ⊤) Γ(B, ⊤) →
        PrimeSpectrum.comap (t ≫ pullback.snd f f).appTop.hom P ∈
          Algebra.unramifiedLocus (Scalars f) Γ(J.subscheme, ⊤)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  let _ := hft
  apply originalBoundary_kernel_of_associated_differential_annihilators e J hJ t h
  intro P hP
  exact ScalarDifferentialPrincipalRigidity.exists_annihilator
    (PrimeSpectrum.comap (t ≫ pullback.snd f f).appTop.hom ⟨P, hP.isPrime⟩)
    (hU ⟨P, hP.isPrime⟩ hP)

end FLT.Mazur.EquivalenceRelationOrderedFrames
