/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleSectionRotation
public import FLT.Mazur.PolygonVeroneseGrading

/-!
# Rotation on every original compatible Veronese algebra

The canonical cyclic pullback acts on the finite direct sum of retained degrees.
It preserves the actual internal grading and every original stage evaluation.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleSectionRotation compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Cyclic pullback restricted to an original compatible homogeneous degree. -/
def compatibleRotationDegreeMap (a : ZMod n) (d : ℕ) :
    compatibleSectionDegree R n h d →+ compatibleSectionDegree R n h d where
  toFun s := ⟨compatibleSectionRotation R n h a s,
    compatibleSectionRotation_degree R n h a d s.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add (compatibleSectionRotation R n h a) s.val t.val)

variable (q : ℕ)

/-- Rotation on the actual finite direct sum of retained compatible degrees. -/
def compatibleVeroneseRotation (a : ZMod n) :
    CompatibleVeroneseSections R n h q →+* CompatibleVeroneseSections R n h q :=
  DirectSum.toSemiring
    (fun d ↦ (DirectSum.of (compatibleVeroneseDegree R n h q ·) d).comp
      (compatibleRotationDegreeMap R n h a (q * d)))
    (by
      change DirectSum.of (compatibleVeroneseDegree R n h q ·) 0
        (compatibleRotationDegreeMap R n h a (q * 0)
          (1 : compatibleVeroneseDegree R n h q 0)) = 1
      have he : compatibleRotationDegreeMap R n h a (q * 0)
          (1 : compatibleVeroneseDegree R n h q 0) =
            (1 : compatibleVeroneseDegree R n h q 0) :=
        Subtype.ext (map_one (compatibleSectionRotation R n h a))
      rw [he, DirectSum.of_zero_one])
    (by
      intro i j s t
      change DirectSum.of (compatibleVeroneseDegree R n h q ·) (i + j)
        (compatibleRotationDegreeMap R n h a (q * (i + j)) _) =
        DirectSum.of (compatibleVeroneseDegree R n h q ·) i
        (compatibleRotationDegreeMap R n h a (q * i) s) *
          DirectSum.of (compatibleVeroneseDegree R n h q ·) j
        (compatibleRotationDegreeMap R n h a (q * j) t)
      rw [DirectSum.of_mul_of]
      congr 1
      exact Subtype.ext (map_mul (compatibleSectionRotation R n h a) s.val t.val))

/-- Rotation retains the original insertion of every homogeneous section. -/
theorem compatibleVeroneseRotation_of (a : ZMod n) (d : ℕ)
    (s : compatibleVeroneseDegree R n h q d) :
    compatibleVeroneseRotation R n h q a (DirectSum.of _ d s) =
      DirectSum.of (compatibleVeroneseDegree R n h q ·) d
        (compatibleRotationDegreeMap R n h a (q * d) s) :=
  DirectSum.toSemiring_of (A := (compatibleVeroneseDegree R n h q ·)) _ _ _ d s

/-- Every retained stage evaluation is the actual original cyclic section pullback. -/
theorem compatibleVeroneseRotation_eval (a : ZMod n) (m : ℕ)
    (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseEval R n h q m (compatibleVeroneseRotation R n h q a s) =
      boundarySectionsRotation R n h m a (compatibleVeroneseEval R n h q m s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseRotation_of, compatibleVeroneseEval_of, compatibleVeroneseEval_of]
    exact compatibleSectionRotation_eval R n h a m s
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The cyclic pullback preserves the actual internal Veronese grading. -/
theorem compatibleVeroneseRotation_mem_grade (a : ZMod n) (d : ℕ)
    {s : CompatibleVeroneseSections R n h q} (hs : s ∈ compatibleVeroneseGrade R n h q d) :
    compatibleVeroneseRotation R n h q a s ∈ compatibleVeroneseGrade R n h q d := by
  obtain ⟨s, rfl⟩ := hs
  exact ⟨_, (compatibleVeroneseRotation_of R n h q a d s).symm⟩

end FLT.Mazur.PolygonInfinitesimalStages
