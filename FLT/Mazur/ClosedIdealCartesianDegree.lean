/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Cartesian restriction of closed families and their degree

Restricting an actual ideal along a cartesian ambient chart gives the base
change of its closed family. Finite locally free degree follows from that
square, without assuming any properties of the restricted quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A B X Y : Scheme.{u}} (J : B.IdealSheafData) (a : A ⟶ B)

/-- The actual restricted closed family maps to the original closed family. -/
def restrictionMap : (J.comap a).subscheme ⟶ J.subscheme :=
  subschemeMap _ _ a (J.le_map_comap a)

/-- The restricted family map preserves its closed immersion. -/
@[reassoc]
theorem restrictionMap_immersion :
    restrictionMap J a ≫ J.subschemeι = (J.comap a).subschemeι ≫ a :=
  subschemeMap_subschemeι _ _ _ _

/-- Restriction of the full ideal is cartesian on actual closed families. -/
theorem restrictionMap_isPullback :
    IsPullback (J.comap a).subschemeι (restrictionMap J a) a J.subschemeι := by
  apply isPullback_of_isClosedImmersion _ _ _ _ (restrictionMap_immersion J a).symm
  rw [ker_subschemeι, ker_subschemeι]

/-- A cartesian ambient chart restricts the closed family by the same base change. -/
theorem restrictionMap_base_isPullback {p : A ⟶ X} {q : B ⟶ Y} {b : X ⟶ Y}
    (h : IsPullback a p q b) :
    IsPullback (restrictionMap J a) ((J.comap a).subschemeι ≫ p)
      (J.subschemeι ≫ q) b :=
  (restrictionMap_isPullback J a).flip.paste_vert h

/-- Finite locally free degree passes to the full restricted ideal family. -/
theorem restriction_degree {p : A ⟶ X} {q : B ⟶ Y} {b : X ⟶ Y}
    (h : IsPullback a p q b) (d : ℕ) (hJ : FCurve.FiniteLocallyFreeDegree
      (J.subschemeι ≫ q) d) :
    FCurve.FiniteLocallyFreeDegree ((J.comap a).subschemeι ≫ p) d :=
  FCurve.finiteLocallyFreeDegree_of_isPullback (restrictionMap_base_isPullback J a h) d hJ

end FLT.Mazur.ClosedIdealCover
