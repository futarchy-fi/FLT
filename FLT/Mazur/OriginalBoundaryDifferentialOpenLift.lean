/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAssociatedComparisonLift
public import FLT.Mazur.OriginalBoundaryDifferentialIdealPower
public import FLT.Mazur.PrincipalIdealComparisonLift

/-!
# Constructed full original arrows on the differential open

Actual comparison coverage constructs an arrow on the complement of the
entire pulled differential ideal. No unramified-locus or essential-finite-type
hypothesis is supplied. The remaining closed locus is explicit and retains
all associated and embedded points where differential rigidity fails.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout PrincipalIdealComparisonLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  (J : A.IdealSheafData)
local instance differentialOpenBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism

/-- A concrete open defined by the differential annihilator of the exact scalar image. -/
def originalBoundaryDifferentialOpen (t : B ⟶ pullback f f) : B.Opens :=
  let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
  idealOpen (t ≫ pullback.snd f f).appTop.hom
    (Module.annihilator Γ(J.subscheme, ⊤)
      (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤)))

omit [IsAffine A] in
/-- Its closed complement is exactly the full pulled differential zero locus. -/
theorem originalBoundary_differentialOpen_complement (t : B ⟶ pullback f f) :
    (originalBoundaryDifferentialOpen J t : Set B)ᶜ = B.toSpecΓ ⁻¹'
      PrimeSpectrum.zeroLocus (originalBoundaryTestDifferentialIdeal J t : Set Γ(B, ⊤)) :=
  complement_idealOpen _ _

omit [IsAffine A] in
/-- Test-linear differential combinations also lie in the constructed open. -/
theorem originalBoundary_differentialCombination_open (t : B ⟶ pullback f f)
    (b : Γ(B, ⊤)) (hb : b ∈ originalBoundaryTestDifferentialIdeal J t) :
    B.basicOpen b ≤ originalBoundaryDifferentialOpen J t :=
  basicOpen_le_idealOpen _ _ b hb

variable [Etale p] [IsAffine B] [IsNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι

include e

/-- Full comparison arrows are constructed on the whole differential open, with both endpoints. -/
theorem originalBoundary_differentialOpen_unique_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c) :
    ∃! d : (originalBoundaryDifferentialOpen J t).toScheme ⟶ pullback p J.subschemeι,
      d ≫ c = (originalBoundaryDifferentialOpen J t).ι ≫ t := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply PrincipalIdealComparisonLift.existsUnique_lift
  exact originalBoundary_differential_principal_lift e J hJ t h

/-- Arbitrary test-linear differential combinations construct actual principal arrows. -/
theorem originalBoundary_differentialCombination_unique_lift
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (b : Γ(B, ⊤)) (hb : b ∈ originalBoundaryTestDifferentialIdeal J t) :
    ∃! d : (B.basicOpen b).toScheme ⟶ pullback p J.subschemeι,
      d ≫ c = (B.basicOpen b).ι ≫ t := by
  obtain ⟨d, hd, _⟩ := originalBoundary_differentialOpen_unique_lift J e hJ t h
  let j := B.homOfLE (originalBoundary_differentialCombination_open J t b hb)
  have he : (j ≫ d) ≫ c = (B.basicOpen b).ι ≫ t := by
    rw [Category.assoc, hd, ← Category.assoc, Scheme.homOfLE_ι]
  let _ := originalBoundaryComparison_mono e J hJ
  exact ⟨j ≫ d, he, fun d' hd' ↦ (cancel_mono c).mp (hd'.trans he.symm)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
