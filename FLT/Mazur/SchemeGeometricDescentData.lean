/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTripleOverlap
public import FLT.Mazur.SchemeOverlapRefinementDiagonal
public import FLT.Mazur.SchemeOverlapRefinementTripleCocycle

/-!
# Geometric module descent data on schemes

A datum consists of an actual double-overlap isomorphism with its diagonal
and canonical triple-overlap equations. Refinement constructs both laws.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemeTripleOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X) (M : Y.Modules)

/-- The isomorphism on the actual categorical double overlap. -/
abbrev Overlap :=
  (pullback (Limits.pullback.fst p p)).obj M ≅
    (pullback (Limits.pullback.snd p p)).obj M

/-- The diagonal equation on the actual categorical double overlap. -/
abbrev Diagonal (e : Overlap p M) : Prop :=
  SchemeOverlapDiagonalChart.DiagonalCompatible _ _ _
    (Limits.pullback.diagonal_fst p) (Limits.pullback.diagonal_snd p) M e

/-- The cocycle equation on the actual categorical triple overlap. -/
abbrev Cocycle (e : Overlap p M) : Prop :=
  SchemeOverlapCocycleChart.CocycleCompatible
    (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (pair12 p) (pair23 p) (pair13 p) (coord1 p) (coord2 p) (coord3 p)
    rfl rfl (pair23_fst p) rfl (pair13_fst p) (pair13_snd p) M e

/-- A geometric descent datum, with equations on the diagonal and triple overlap. -/
structure Data where
  /-- The actual overlap isomorphism. -/
  overlap : Overlap p M
  /-- Its restriction to the diagonal is the identity. -/
  diagonal : Diagonal p M overlap
  /-- Its three restrictions satisfy the cocycle. -/
  cocycle : Cocycle p M overlap

namespace Data
variable {M} (D : Data p M)
variable {X' Y' : Scheme.{u}} (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- Restrict a geometric datum along any commutative scheme square. -/
def refine : Data q ((pullback b).obj M) where
  overlap := SchemeOverlapRefinement.refine p q a b w D.overlap
  diagonal := SchemeOverlapRefinement.refine_diagonal p q a b w M D.overlap D.diagonal
  cocycle := SchemeOverlapRefinementCocycle.refine_cocycle_of_squares p q a b w
    (pair12 p) (pair23 p) (pair13 p) (coord1 p) (coord2 p) (coord3 p)
    rfl rfl (pair23_fst p) rfl (pair13_fst p) (pair13_snd p)
    (pair12 q) (pair23 q) (pair13 q) (coord1 q) (coord2 q) (coord3 q)
    rfl rfl (pair23_fst q) rfl (pair13_fst q) (pair13_snd q)
    (refinement p q a b w) (refinement_coord1 p q a b w)
    (refinement_coord2 p q a b w) (refinement_coord3 p q a b w)
    (refinement_pair12 p q a b w) (refinement_pair23 p q a b w)
    (refinement_pair13 p q a b w) M D.overlap D.cocycle

/-- The refined datum has the prescribed geometric overlap. -/
theorem refine_overlap :
    (D.refine p q a b w).overlap = SchemeOverlapRefinement.refine p q a b w D.overlap := rfl

/-- A morphism of geometric data is a map intertwining the actual overlaps. -/
def MapCompatible {N : Y.Modules} (E : Data p N) (f : M ⟶ N) : Prop :=
  D.overlap.hom ≫ (pullback (Limits.pullback.snd p p)).map f =
    (pullback (Limits.pullback.fst p p)).map f ≫ E.overlap.hom

/-- Geometric refinement preserves compatible morphisms. -/
theorem refine_mapCompatible {N : Y.Modules} (E : Data p N) (f : M ⟶ N)
    (hf : D.MapCompatible p E f) :
    (D.refine p q a b w).MapCompatible q (E.refine p q a b w) ((pullback b).map f) :=
  SchemeOverlapRefinement.refine_compatible p q a b w D.overlap E.overlap f hf

end Data
end FLT.Mazur.SchemeGeometricDescent
