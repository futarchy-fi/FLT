/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorGeometricPowers
public import FLT.Mazur.CartierGeneratorUnitPowers
public import Mathlib.Data.Nat.Totient

/-!
# Finite geometric choices of Cartier generator

The full-level unit group surjects onto the actual Cartier generators over
an algebraically closed field. Their number is at most the totient of the
level; no injectivity of the original cyclic marking is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {K : Type} [Field K] [IsAlgClosed K]
  {E : GeneralizedEllipticCurve (Spec (.of K))} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n)

/-- All actual Cartier generators of the original geometric subgroup. -/
abbrev GeometricGenerators :=
  {P : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier // H.IsCartierGenerator P}

variable {P : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- Full-level units produce actual Cartier generators, retaining every divisor multiplicity. -/
def geometricGeneratorUnitMap (u : (ZMod n)ˣ) : H.GeometricGenerators :=
  ⟨P ^ u.val.val, hP.pow_unit H u⟩

/-- Every geometric Cartier generator lies in the single full-level unit orbit. -/
theorem geometricGeneratorUnitMap_surjective :
    Function.Surjective (H.geometricGeneratorUnitMap hP) := by
  intro Q
  obtain ⟨u, hu⟩ := hP.exists_unit_power H Q.property
  exact ⟨u, Subtype.ext hu⟩

/-- The full geometric generator set is finite, including for non-etale subgroup schemes. -/
instance geometricGenerators_finite : Finite H.GeometricGenerators := by
  classical
  by_cases h : Nonempty H.GeometricGenerators
  · obtain ⟨P⟩ := h
    exact Finite.of_surjective _ (H.geometricGeneratorUnitMap_surjective P.property)
  · have : IsEmpty H.GeometricGenerators := not_nonempty_iff.mp h
    exact Finite.of_subsingleton

/-- An explicit bound on all geometric generator choices at the original level. -/
theorem geometricGenerators_card_le_totient : Nat.card H.GeometricGenerators ≤ n.totient := by
  classical
  by_cases h : Nonempty H.GeometricGenerators
  · obtain ⟨P⟩ := h
    have hb := Nat.card_le_card_of_surjective _
      (H.geometricGeneratorUnitMap_surjective P.property)
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using hb
  · have : IsEmpty H.GeometricGenerators := not_nonempty_iff.mp h
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
