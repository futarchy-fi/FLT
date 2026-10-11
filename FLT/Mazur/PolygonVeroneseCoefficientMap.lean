/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleGradedCoefficientMap
public import FLT.Mazur.PolygonVeroneseGrading
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Coefficient maps on every original compatible Veronese algebra

The constructed degree-preserving compatible map induces a ring map on the
finite direct sums of retained homogeneous pieces, retaining the original evaluations.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleCoefficientMap compatibleEval
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- The original coefficient pullback on the direct sum of all compatible degrees. -/
def compatibleVeroneseCoefficientMap :
    CompatibleVeroneseSections R n h q →+* CompatibleVeroneseSections S n h q :=
  DirectSum.toSemiring
    (fun d ↦ (DirectSum.of (compatibleVeroneseDegree S n h q ·) d).comp
      (compatibleCoefficientDegreeMap f n h (q * d)))
    (by
      change DirectSum.of (compatibleVeroneseDegree S n h q ·) 0
        (compatibleCoefficientDegreeMap f n h (q * 0)
          (1 : compatibleVeroneseDegree R n h q 0)) = 1
      have he : compatibleCoefficientDegreeMap f n h (q * 0)
          (1 : compatibleVeroneseDegree R n h q 0) =
            (1 : compatibleVeroneseDegree S n h q 0) :=
        Subtype.ext (map_one (compatibleCoefficientMap f n h))
      rw [he, DirectSum.of_zero_one])
    (by
      intro i j s t
      change DirectSum.of (compatibleVeroneseDegree S n h q ·) (i + j)
        (compatibleCoefficientDegreeMap f n h (q * (i + j)) _) =
        DirectSum.of (compatibleVeroneseDegree S n h q ·) i
        (compatibleCoefficientDegreeMap f n h (q * i) s) *
          DirectSum.of (compatibleVeroneseDegree S n h q ·) j
        (compatibleCoefficientDegreeMap f n h (q * j) t)
      rw [DirectSum.of_mul_of]
      congr 1
      exact Subtype.ext (map_mul (compatibleCoefficientMap f n h) s.val t.val))

/-- Each homogeneous insertion retains its original degree and coefficient pullback. -/
theorem compatibleVeroneseCoefficientMap_of (d : ℕ) (s : compatibleVeroneseDegree R n h q d) :
    compatibleVeroneseCoefficientMap f n h q
      (DirectSum.of (compatibleVeroneseDegree R n h q ·) d s) =
      DirectSum.of (compatibleVeroneseDegree S n h q ·) d
        (compatibleCoefficientDegreeMap f n h (q * d) s) :=
  DirectSum.toSemiring_of (A := (compatibleVeroneseDegree R n h q ·)) _ _ _ d s

/-- The graded map retains every actual stage section evaluation. -/
theorem compatibleVeroneseCoefficientMap_eval (m : ℕ) (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseEval S n h q m (compatibleVeroneseCoefficientMap f n h q s) =
      coefficientBoundarySections f m n h (compatibleVeroneseEval R n h q m s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseCoefficientMap_of, compatibleVeroneseEval_of, compatibleVeroneseEval_of]
    exact compatibleCoefficientMap_eval f n h m s
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The retained coefficient map is graded for the actual internal Veronese gradings. -/
def compatibleVeroneseCoefficientGradedMap :
    compatibleVeroneseGrade R n h q →+*ᵍ compatibleVeroneseGrade S n h q where
  __ := compatibleVeroneseCoefficientMap f n h q
  map_mem := by
    intro d s hs
    obtain ⟨s, rfl⟩ := hs
    exact ⟨_, (compatibleVeroneseCoefficientMap_of f n h q d s).symm⟩

end FLT.Mazur.PolygonInfinitesimalStages
