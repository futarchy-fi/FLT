/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularProductBaseChange
public import FLT.Mazur.FiniteFlatIdealVanishingUniversal

/-!
# The closed multiplication locus for singular cyclic markings

The coefficient ideal on the original base represents multiplication closure
on the full orbit product. Its universal property includes nonflat tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]

/-- The global coefficient ideal of the full singular orbit multiplication equation. -/
def singularOrbitCoefficientIdeal : S.IdealSheafData :=
  FiniteFlatIdealVanishing.idealSheaf (E.singularOrbitProduct φ).hom
    (E.singularOrbitMultiplicationIdeal φ)

/-- The closed multiplication locus in the original parameter scheme. -/
def singularOrbitLocus : Scheme :=
  FiniteFlatIdealVanishing.locus (E.singularOrbitProduct φ).hom
    (E.singularOrbitMultiplicationIdeal φ)

/-- The actual closed immersion of the equation locus. -/
def singularOrbitLocusInclusion : E.singularOrbitLocus φ ⟶ S :=
  FiniteFlatIdealVanishing.locusInclusion (E.singularOrbitProduct φ).hom
    (E.singularOrbitMultiplicationIdeal φ)

instance singularOrbitLocusInclusion_closed : IsClosedImmersion (E.singularOrbitLocusInclusion φ) :=
  FiniteFlatIdealVanishing.locusInclusion_closed _ _

variable (g : T ⟶ S)
local instance singularLocusPullback_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

/-- The global coefficient sheaf itself commutes with arbitrary parameter change. -/
theorem singularOrbitCoefficientIdeal_baseChange :
    (E.baseChange g).singularOrbitCoefficientIdeal (pullCyclicMarking (E := E) g φ) =
      (E.singularOrbitCoefficientIdeal φ).comap g := by
  unfold singularOrbitCoefficientIdeal
  rw [singularOrbitMultiplicationIdeal_baseChange]
  exact FiniteFlatIdealVanishing.idealSheaf_baseChange
    (E.singularOrbitProductBaseChangeMap_isPullback φ g) _

/-- A parameter factors through the closed locus exactly when its full equation vanishes. -/
theorem singularOrbitLocus_factorization_iff :
    (∃ k : T ⟶ E.singularOrbitLocus φ, k ≫ E.singularOrbitLocusInclusion φ = g) ↔
      ClosedGroupIdeal.multiplicationEquation (E.baseChange g).group
        ((E.baseChange g).cyclicMarkingGroupIdeal (pullCyclicMarking (E := E) g φ)) = 0 := by
  rw [(E.baseChange g).singularOrbitMultiplication_iff_ideal,
    singularOrbitMultiplicationIdeal_baseChange]
  exact FiniteFlatIdealVanishing.locus_factorization_iff
    (E.singularOrbitProductBaseChangeMap_isPullback φ g) _

/-- The closed locus represents the exact original orbit-subgroup condition on all tests. -/
theorem singularOrbitLocus_factorization_iff_subgroup [NeZero n] :
    (∃ k : T ⟶ E.singularOrbitLocus φ, k ≫ E.singularOrbitLocusInclusion φ = g) ↔
      ∃ H : (E.baseChange g).FiniteSubgroup n,
        H.ideal = (E.baseChange g).cyclicMarkingIdeal (pullCyclicMarking (E := E) g φ) := by
  rw [singularOrbitLocus_factorization_iff]
  exact (E.baseChange g).singularCyclicDivisorMultiplication_iff_subgroup _

end FLT.Mazur.GeneralizedEllipticCurve
