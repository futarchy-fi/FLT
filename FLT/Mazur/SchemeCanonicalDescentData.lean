/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalOverlapDiagonal
public import FLT.Mazur.SchemeCanonicalOverlapCocycle
public import FLT.Mazur.SchemeCanonicalOverlapNaturality
public import FLT.Mazur.SchemeGeometricDescentData

/-!
# Canonical geometric descent data on a pulled-back module sheaf

The canonical overlap satisfies the actual diagonal and triple cocycle laws.
Every base sheaf morphism pulls back to a compatible morphism of these data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemePullbackOverlap SchemeTripleOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Canonical descent datum on the pullback of an arbitrary base module sheaf. -/
def canonical (A : X.Modules) : Data p ((pullback p).obj A) where
  overlap := SchemePullbackOverlap.overlap p (Limits.pullback.fst p p)
    (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
    rfl Limits.pullback.condition.symm A
  diagonal := overlap_diagonal p _ _ _ rfl Limits.pullback.condition.symm
    (Limits.pullback.diagonal p) (Limits.pullback.diagonal_fst p)
    (Limits.pullback.diagonal_snd p) A
  cocycle := overlap_cocycle p _ _ _ rfl Limits.pullback.condition.symm
    (pair12 p) (pair23 p) (pair13 p) (coord1 p) (coord2 p) (coord3 p)
    rfl rfl (pair23_fst p) rfl (pair13_fst p) (pair13_snd p) A

/-- Every base map induces a compatible map of canonical descent data. -/
lemma canonical_mapCompatible {A B : X.Modules} (f : A ⟶ B) :
    (canonical p A).MapCompatible p (canonical p B) ((pullback p).map f) :=
  overlap_naturality p _ _ _ rfl Limits.pullback.condition.symm f

end FLT.Mazur.SchemeGeometricDescent
