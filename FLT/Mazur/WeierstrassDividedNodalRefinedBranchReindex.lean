/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchLift

/-!
# Intermediate outputs with an independently indexed target datum

An explicit equality of depths transports the actual algebra map and its
contraction. This keeps finite-family indices out of coordinate-ring casts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k r l : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k) (e : Data W π l) (hl : l = k + r)
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S) [Module.Flat R S]
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "res" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c

/-- Transport the constructed algebra map to an independently indexed target datum. -/
def nodalRefinedBranchReindexedOutput : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] B := by
  subst l
  exact nodalRefinedBranchOutput D d hdepth hrk hrm e a2 h2 a c

/-- The transported map gives an actual target chart morphism. -/
def nodalRefinedBranchReindexedLift : Spec (.of B) ⟶ chart e :=
  Spec.map (CommRingCat.ofHom
    (nodalRefinedBranchReindexedOutput D d hdepth hrk hrm e hl a2 h2 a c).toRingHom)

/-- Reindexing preserves the exact original tangent sum. -/
@[reassoc] theorem nodalRefinedBranchReindexedLift_contraction :
    nodalRefinedBranchReindexedLift D d hdepth hrk hrm e hl a2 h2 a c ≫ toCurve e =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  subst l
  exact nodalRefinedBranchLift_contraction D d hdepth hrk hrm e a2 h2 a c

/-- Reindexing preserves the original coefficient map. -/
@[reassoc] theorem nodalRefinedBranchReindexedLift_structure :
    nodalRefinedBranchReindexedLift D d hdepth hrk hrm e hl a2 h2 a c ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
