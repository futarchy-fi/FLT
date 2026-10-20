/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientEmbedding
public import FLT.Mazur.OneGonAdicCanonicalSubgroup

/-!
# A finite-presentation coefficient base for the actual adic subgroup

The canonical complete-base coordinate map selects finite integer coefficients.
The complementary discriminant inverse is retained, so the descended whole
cubic is an actual generalized elliptic curve. Its character embedding has
surjective coordinates before extending back to the complete ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart OneGonFiniteCoefficientCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The exact original canonical character coordinates. -/
def canonicalCoordinates : Coordinate (equation t) 1 →ₐ[R] AddMonoidAlgebra R (ZMod n) :=
  effectiveCoordinates I t ht (initialRootsHom n I t ht)

/-- The canonical full coordinate map is surjective, without Noetherian hypotheses. -/
theorem canonicalCoordinates_surjective : Function.Surjective (canonicalCoordinates I t ht n) :=
  effectiveCoordinates_surjective I t ht _ (towerCoordinates_zero_surjective I t ht _)

/-- The actual inverse of the complementary discriminant factor. -/
def complementaryInverse : R := ↑(complementaryFactor_isUnit I t ht).unit⁻¹

/-- The chosen inverse satisfies the original exact equation. -/
theorem complementaryInverse_mul : complementaryInverse I t ht * (1 + 432 * t) = 1 := by
  exact (congrArg (fun x : R => complementaryInverse I t ht * x)
    (complementaryFactor_isUnit I t ht).unit_spec).symm.trans
      (Units.inv_mul (complementaryFactor_isUnit I t ht).unit)

/-- Finite coefficients retaining surjectivity and the complementary discriminant inverse exist. -/
theorem exists_algebraicSupport :
    ∃ s : Set R, s.Finite ∧ {complementaryInverse I t ht} ⊆ s ∧
      Function.Surjective (modelCoordinates t 1 (canonicalCoordinates I t ht n) s) :=
  exists_surjective_model t 1 _ (canonicalCoordinates_surjective I t ht n)
    {complementaryInverse I t ht} (Set.finite_singleton _)

/-- A chosen finite support of the actual canonical embedding. -/
def algebraicSupport : Set R := (exists_algebraicSupport I t ht n).choose

/-- The chosen support is finite. -/
theorem algebraicSupport_finite : (algebraicSupport I t ht n).Finite :=
  (exists_algebraicSupport I t ht n).choose_spec.1

/-- It retains the original inverse, rather than merely inverting a new formal parameter. -/
theorem complementaryInverse_mem : complementaryInverse I t ht ∈ algebraicSupport I t ht n :=
  (exists_algebraicSupport I t ht n).choose_spec.2.1 rfl

/-- The selected model coordinate map is already surjective. -/
theorem algebraicCoordinates_surjective : Function.Surjective
    (modelCoordinates t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n)) :=
  (exists_algebraicSupport I t ht n).choose_spec.2.2

/-- The finite-type integer subring of the actual complete coefficient ring. -/
abbrev algebraicBase : Subalgebra ℤ R :=
  modelRing t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n)

/-- The original smoothing parameter over its finite coefficient base. -/
def algebraicParameter : algebraicBase I t ht n :=
  modelParameter t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n)

/-- The selected coefficient ring is finite type over the integers. -/
instance algebraicBase_finiteType : Algebra.FiniteType ℤ (algebraicBase I t ht n) :=
  modelRing_finiteType t 1 _ _ (algebraicSupport_finite I t ht n)

/-- The selected base is finitely presented over the integers. -/
instance algebraicBase_finitePresentation :
    Algebra.FinitePresentation ℤ (algebraicBase I t ht n) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- The actual complementary discriminant factor is a unit already on the model base. -/
theorem algebraicParameter_complementaryUnit : IsUnit (1 + 432 * algebraicParameter I t ht n) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨complementaryInverse I t ht,
    CharacterFiniteCoefficientModel.subset_coefficientRing _ _
      (Or.inl (complementaryInverse_mem I t ht n))⟩, ?_⟩
  apply Subtype.ext
  change (1 + 432 * t) * complementaryInverse I t ht = 1
  rw [mul_comm, complementaryInverse_mul]

/-- The descended whole cubic is a genuine generalized elliptic curve. -/
def algebraicCurve : GeneralizedEllipticCurve (Spec (.of (algebraicBase I t ht n))) :=
  ArithmeticOneGonGeneralizedCurve.curve (algebraicParameter I t ht n)
    (algebraicParameter_complementaryUnit I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
