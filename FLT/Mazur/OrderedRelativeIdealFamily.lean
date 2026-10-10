/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorRank
public import FLT.Mazur.OrderedCurvePermutation
public import FLT.Mazur.RelativeIdealFamilies

/-!
# The ordered divisor as a full relative ideal family

The symmetry of the actual fiber product transports the existing ordered
graph-product divisor into the Hilbert family's base-first convention.
Its degree, repeated points, and empty tuples are preserved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

namespace FLT.Mazur.OrderedCurvePower

set_option backward.isDefEq.respectTransparency false

variable {Z S X : Scheme.{0}} (z : Z ⟶ S) (d : ℕ)
variable [SmoothOfRelativeDimension 1 z] [IsProper z]
variable (s : X ⟶ S) (x : Fin d → (X ⟶ Z)) (hx : ∀ i, x i ≫ z = s)

/-- The full ideal family of an ordered tuple, transported by actual pullback symmetry. -/
def tupleRelativeIdealFamily : RelativeIdealFamilies z d s :=
  ⟨(tupleDivisorIdeal z d s x hx).comap (pullbackSymmetry s z).hom,
    restriction_degree _ _ (b := 𝟙 X) (IsPullback.of_horiz_isIso ⟨by simp⟩) d
      (tupleDivisor_finiteLocallyFreeDegree z d s x hx)⟩

/-- Reindexing a tuple preserves the full ideal, including its multiplicities. -/
theorem tupleRelativeIdealFamily_permutation (σ : Equiv.Perm (Fin d)) :
    tupleRelativeIdealFamily z d s (fun i ↦ x (σ i)) (fun i ↦ hx (σ i)) =
      tupleRelativeIdealFamily z d s x hx := by
  apply Subtype.ext
  change (∏ i : Fin d, (CurveGraphPullback.graph z s (x (σ i)) (hx (σ i))).ker).comap _ = _
  rw [Equiv.prod_comp σ (fun i ↦ (CurveGraphPullback.graph z s (x i) (hx i)).ker)]
  rfl

/-- The full universal ordered family in the Hilbert ambient convention. -/
def orderedRelativeIdealFamily : RelativeIdealFamilies z d (base z d) :=
  tupleRelativeIdealFamily z d (base z d) (point z d) (point_base z d)

/-- The universal full ideal is exactly the transported original graph-product ideal. -/
theorem orderedRelativeIdealFamily_val :
    (orderedRelativeIdealFamily z d).val =
      (divisorIdeal z d).comap (pullbackSymmetry (base z d) z).hom := rfl

end FLT.Mazur.OrderedCurvePower
