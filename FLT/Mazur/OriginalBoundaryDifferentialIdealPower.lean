/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealMapPowerAnnihilator
public import FLT.Mazur.OriginalBoundaryDifferentialKernelSupport

/-!
# The full differential obstruction ideal on an original coefficient test

The extended ideal of all original comparison equations is annihilated by
one power of the entire pulled differential ideal, whenever that test ideal
is finitely generated. This controls every linear combination of differential
annihilators simultaneously, without finite generation of the scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance differentialIdealBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism


/-- The unchanged full comparison equations extended to the actual test coefficients. -/
def originalBoundaryTestEquationIdeal (t : B ⟶ pullback f f) : Ideal Γ(B, ⊤) :=
  (RingHom.ker (c).appTop.hom).map t.appTop.hom

omit e hJ in
/-- All exact scalar differential annihilators pulled to the second test endpoint. -/
def originalBoundaryTestDifferentialIdeal (t : B ⟶ pullback f f) : Ideal Γ(B, ⊤) :=
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  (Module.annihilator Γ(J.subscheme, ⊤)
    (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))).map
      (t ≫ pullback.snd f f).appTop.hom

include e

/-- The whole differential ideal lies in the radical of the full equation annihilator. -/
theorem originalBoundary_differentialIdeal_le_radical
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c) :
    originalBoundaryTestDifferentialIdeal J t ≤
      (originalBoundaryTestEquationIdeal J hJ t).annihilator.radical := by
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  apply IdealMapPowerAnnihilator.map_le_radical_annihilator
  intro a ha
  exact originalBoundary_differential_uniform_kernel e J hJ t h a ha

/-- Finite generation on the test gives one power for all differential combinations. -/
theorem originalBoundary_differentialIdeal_power
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (hfg : (originalBoundaryTestDifferentialIdeal J t).FG) :
    ∃ k : ℕ, originalBoundaryTestDifferentialIdeal J t ^ k ≤
      (originalBoundaryTestEquationIdeal J hJ t).annihilator :=
  Ideal.exists_pow_le_of_le_radical_of_fg
    (originalBoundary_differentialIdeal_le_radical e J hJ t h) hfg

/-- Noetherian test coordinates construct the required finite generation. -/
theorem originalBoundary_differentialIdeal_power_of_noetherian
    [IsNoetherianRing Γ(B, ⊤)] (t : B ⟶ pullback f f)
    (h : Set.range t ⊆ Set.range c) :
    ∃ k : ℕ, originalBoundaryTestDifferentialIdeal J t ^ k ≤
      (originalBoundaryTestEquationIdeal J hJ t).annihilator :=
  originalBoundary_differentialIdeal_power e J hJ t h (IsNoetherian.noetherian _)

/-- The support of all full equations lies in the actual pulled differential closed set. -/
theorem originalBoundary_equation_support_subset_differential
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c) :
    PrimeSpectrum.zeroLocus ((originalBoundaryTestEquationIdeal J hJ t).annihilator :
      Set Γ(B, ⊤)) ⊆
      PrimeSpectrum.zeroLocus (originalBoundaryTestDifferentialIdeal J t : Set Γ(B, ⊤)) :=
  (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mpr
    (originalBoundary_differentialIdeal_le_radical e J hJ t h)

end FLT.Mazur.EquivalenceRelationOrderedFrames
