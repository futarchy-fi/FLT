/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleCoefficientScalars

/-!
# Coefficient maps on the actual compatible graded section rings

The constructed degree-preserving compatible map induces a ring map on the
finite direct sums of homogeneous pieces, retaining the original evaluations.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleCoefficientMap compatibleEval
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n)

/-- The coefficient pullback on each compatible homogeneous piece. -/
def compatibleCoefficientDegreeMap (d : ℕ) :
    compatibleSectionDegree R n h d →+ compatibleSectionDegree S n h d where
  toFun s := ⟨compatibleCoefficientMap f n h s, compatibleCoefficientMap_degree f n h d s.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add (compatibleCoefficientMap f n h) s.val t.val)

/-- The original coefficient pullback on the direct sum of all compatible degrees. -/
def compatibleGradedCoefficientMap :
    CompatibleGradedSections R n h →+* CompatibleGradedSections S n h :=
  DirectSum.toSemiring
    (fun d ↦ (DirectSum.of (compatibleSectionDegree S n h ·) d).comp
      (compatibleCoefficientDegreeMap f n h d))
    (by
      change DirectSum.of (compatibleSectionDegree S n h ·) 0
        (compatibleCoefficientDegreeMap f n h 0 1) = 1
      have he : compatibleCoefficientDegreeMap f n h 0 1 = 1 := Subtype.ext (map_one _)
      rw [he, DirectSum.of_zero_one])
    (by
      intro i j s t
      change DirectSum.of (compatibleSectionDegree S n h ·) (i + j)
        (compatibleCoefficientDegreeMap f n h (i + j) _) =
        DirectSum.of (compatibleSectionDegree S n h ·) i
        (compatibleCoefficientDegreeMap f n h i s) *
          DirectSum.of (compatibleSectionDegree S n h ·) j
        (compatibleCoefficientDegreeMap f n h j t)
      rw [DirectSum.of_mul_of]
      congr 1
      exact Subtype.ext (map_mul (compatibleCoefficientMap f n h) s.val t.val))

/-- Each homogeneous insertion retains its original degree and coefficient pullback. -/
theorem compatibleGradedCoefficientMap_of (d : ℕ) (s : compatibleSectionDegree R n h d) :
    compatibleGradedCoefficientMap f n h (DirectSum.of (compatibleSectionDegree R n h ·) d s) =
      DirectSum.of (compatibleSectionDegree S n h ·) d
        (compatibleCoefficientDegreeMap f n h d s) :=
  DirectSum.toSemiring_of (A := (compatibleSectionDegree R n h ·)) _ _ _ d s

/-- The graded map retains every actual stage section evaluation. -/
theorem compatibleGradedCoefficientMap_eval (m : ℕ) (s : CompatibleGradedSections R n h) :
    compatibleGradedEval S n h m (compatibleGradedCoefficientMap f n h s) =
      coefficientBoundarySections f m n h (compatibleGradedEval R n h m s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleGradedCoefficientMap_of, compatibleGradedEval_of, compatibleGradedEval_of]
    exact compatibleCoefficientMap_eval f n h m s
  | add s t hs ht => simp only [map_add, hs, ht]

end FLT.Mazur.PolygonInfinitesimalStages
