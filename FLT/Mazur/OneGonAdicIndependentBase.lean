/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFiniteCoefficientBase

/-!
# Arbitrary finite supports for the canonical one-gon

The support is an input, not a fixed choice. Retaining the complementary inverse
constructs an arithmetic generalized curve over each finite coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open OneGonAdicCharacterTower OneGonFiniteCoefficientCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)

/-- The coefficient ring belonging to the supplied support. -/
abbrev base : Subalgebra ℤ R := modelRing t 1 (canonicalCoordinates I t ht n) s

/-- The original smoothing parameter in this independently selected ring. -/
def parameter : base I t ht n s := modelParameter t 1 (canonicalCoordinates I t ht n) s

/-- Every finite support gives a finite-type coefficient ring. -/
theorem base_finiteType (hs : s.Finite) : Algebra.FiniteType ℤ (base I t ht n s) :=
  modelRing_finiteType t 1 _ s hs

/-- These finite coefficient rings are finitely presented over the integers. -/
theorem base_finitePresentation (hs : s.Finite) :
    Algebra.FinitePresentation ℤ (base I t ht n s) := by
  let _ := base_finiteType I t ht n s hs
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Retaining the actual complementary inverse constructs the required unit. -/
theorem parameter_complementaryUnit (hi : complementaryInverse I t ht ∈ s) :
    IsUnit (1 + 432 * parameter I t ht n s) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨complementaryInverse I t ht,
    CharacterFiniteCoefficientModel.subset_coefficientRing _ _ (Or.inl hi)⟩, ?_⟩
  apply Subtype.ext
  change (1 + 432 * t) * complementaryInverse I t ht = 1
  rw [mul_comm, complementaryInverse_mul]

/-- A full generalized one-gon for any support retaining the actual inverse. -/
def curve (hi : complementaryInverse I t ht ∈ s) :
    GeneralizedEllipticCurve (Spec (.of (base I t ht n s))) :=
  ArithmeticOneGonGeneralizedCurve.curve (parameter I t ht n s)
    (parameter_complementaryUnit I t ht n s hi)

/-- The unchanged finite character source over this independent coefficient ring. -/
abbrev carrier : Over (Spec (.of (base I t ht n s))) :=
  CharacterSchemeBaseChange.model (base I t ht n s) (ZMod n)

/-- The source retains exact rank, including in characteristics dividing the order. -/
theorem carrier_degree : FCurve.FiniteLocallyFreeDegree (carrier I t ht n s).hom n :=
  RootsOfUnityScheme.degree _ n

end FLT.Mazur.OneGonAdicIndependentModel
