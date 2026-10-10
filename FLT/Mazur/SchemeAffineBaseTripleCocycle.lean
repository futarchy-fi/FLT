/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestCocycle

/-!
# The full geometric triple-overlap cocycle

The three base charts have a scheme-theoretic triple overlap without any
separation assumption. The glued comparisons compose on this entire scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (T : Fin 3 → Chart p)

/-- The entire geometric intersection of three base charts. -/
abbrev baseTripleOverlap : Scheme.{u} :=
  Limits.pullback (Limits.pullback.fst (T 0).base (T 1).base ≫ (T 0).base) (T 2).base

/-- Map from the triple overlap to the first pair overlap. -/
abbrev baseTripleFirstPair : baseTripleOverlap T ⟶ (T 0).baseOverlap (T 1) :=
  Limits.pullback.fst _ _

/-- The first coordinate of the geometric triple overlap. -/
abbrev baseTripleFirst : baseTripleOverlap T ⟶ Spec (T 0).baseRing :=
  baseTripleFirstPair T ≫ Limits.pullback.fst _ _

/-- The second coordinate of the geometric triple overlap. -/
abbrev baseTripleSecond : baseTripleOverlap T ⟶ Spec (T 1).baseRing :=
  baseTripleFirstPair T ≫ Limits.pullback.snd _ _

/-- The third coordinate of the geometric triple overlap. -/
abbrev baseTripleThird : baseTripleOverlap T ⟶ Spec (T 2).baseRing :=
  Limits.pullback.snd _ _

/-- All three coordinate paths have the same base map. -/
theorem baseTripleSecond_over :
    baseTripleSecond T ≫ (T 1).base = baseTripleFirst T ≫ (T 0).base := by
  simp only [baseTripleSecond, baseTripleFirst, Category.assoc, Limits.pullback.condition]

/-- The third coordinate has the common base map. -/
theorem baseTripleThird_over :
    baseTripleThird T ≫ (T 2).base = baseTripleFirst T ≫ (T 0).base := by
  exact (Limits.pullback.condition).symm.trans (Category.assoc _ _ _).symm

/-- The three coordinates as a dependent family. -/
def baseTripleCoordinates (i : Fin 3) : baseTripleOverlap T ⟶ Spec (T i).baseRing :=
  Fin.cases (baseTripleFirst T)
    (Fin.cases (baseTripleSecond T)
      (Fin.cases (baseTripleThird T) (fun i ↦ i.elim0))) i

/-- The dependent coordinate family lies over the same base map. -/
theorem baseTripleCoordinates_over (i : Fin 3) :
    baseTripleCoordinates T i ≫ (T i).base = baseTripleFirst T ≫ (T 0).base := by
  fin_cases i
  · rfl
  · exact baseTripleSecond_over T
  · exact baseTripleThird_over T

variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf schemeTestComparison

/-- The glued overlap comparison transported to a pair of triple coordinates. -/
def baseTripleComparison (i j : Fin 3) :
    (pullback (baseTripleCoordinates T i)).obj ((T i).sheaf D) ⟶
      (pullback (baseTripleCoordinates T j)).obj ((T j).sheaf D) :=
  (T i).schemeTestComparison (T j) D (baseTripleCoordinates T i)
    (baseTripleCoordinates T j)
    ((baseTripleCoordinates_over T i).trans (baseTripleCoordinates_over T j).symm)

/-- The actual glued overlap maps satisfy the cocycle on the whole triple overlap. -/
theorem baseTripleComparison_cocycle :
    (T 0).schemeTestComparison (T 1) D (baseTripleCoordinates T 0)
        (baseTripleCoordinates T 1)
        ((baseTripleCoordinates_over T 0).trans (baseTripleCoordinates_over T 1).symm) ≫
      (T 1).schemeTestComparison (T 2) D (baseTripleCoordinates T 1)
        (baseTripleCoordinates T 2)
        ((baseTripleCoordinates_over T 1).trans (baseTripleCoordinates_over T 2).symm) =
      (T 0).schemeTestComparison (T 2) D (baseTripleCoordinates T 0)
        (baseTripleCoordinates T 2)
        ((baseTripleCoordinates_over T 0).trans (baseTripleCoordinates_over T 2).symm) :=
  schemeTestComparison_cocycle D T (baseTripleFirst T ≫ (T 0).base)
    (baseTripleCoordinates T) (baseTripleCoordinates_over T)

end FLT.Mazur.SchemeAffineDescent.Chart
