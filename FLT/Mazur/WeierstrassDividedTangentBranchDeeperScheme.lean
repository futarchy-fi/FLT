/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperOutput
public import FLT.Mazur.WeierstrassDividedTangentBranchScheme

/-!
# The actual deeper branch morphism retains the entire old output

Pass the constructed doubled-depth algebra map to schemes and prove exact
refinement, original tangent contraction, and coefficient compatibility.
No smoothness of the deeper output is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "W'" => W.map (algebraMap R B)
local notation "b3B" => algebraMap R B b3

variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')

variable (b3' b6'' : R) (h3' : b3 = s * b3') (h6'' : b6' = s * b6'')
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

local notation "X₂" => dividedTangentBranchDeeperX W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
local notation "Y₂" => dividedTangentBranchDeeperY W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
variable [Module.Flat R S] (hs : IsRegular s)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

local notation "out" => dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6'
  hs h2 h3 h4 h6 h4' h6'

local notation "out₂" => dividedTangentBranchDeeperOutput W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6'' hs h3 h4 h6
local notation "h66" => tangentBranch_deeper_factor6 s b6 b6' h6' b6'' h6''
local notation "r" => refinement W s s b3 b4 b6 b3' b4' b6'' h3' h4' h66
local notation "old" => dividedTangentBranchLift W s b3 b4 b6 a c a2 b4' b6'
  hs h2 h3 h4 h6 h4' h6'
local notation "e" => dividedTangentBranchRestriction W s b3 b4 b6 a c

/-- The actual scheme-valued branch output at doubled depth. -/
def dividedTangentBranchDeeperLift : Spec (.of B) ⟶
    Spec (.of (Coordinate W (s * s) b3' b4' b6'')) :=
  Spec.map (CommRingCat.ofHom (out₂).toRingHom)

local notation "v" => dividedTangentBranchDeeperLift W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6'' hs h3 h4 h6

/-- The entire prior divided output is the refinement of the deeper scheme output. -/
@[reassoc] theorem dividedTangentBranchDeeperLift_refinement :
    v ≫ Spec.map (CommRingCat.ofHom (r).toRingHom) = old := by
  rw [dividedTangentBranchDeeperLift, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((out₂).comp r).toRingHom) = _
  rw [dividedTangentBranchDeeperOutput_refinement]
  rfl

/-- Contracting through the older chart retains exactly the original tangent sum. -/
@[reassoc] theorem dividedTangentBranchDeeperLift_contraction :
    v ≫ Spec.map (CommRingCat.ofHom (r).toRingHom) ≫ toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  rw [dividedTangentBranchDeeperLift_refinement_assoc, dividedTangentBranchLift_contraction]

/-- The deeper chart retains the coefficient point on the same entire branch source. -/
@[reassoc] theorem dividedTangentBranchDeeperLift_structure :
    v ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (s * s) b3' b4' b6''))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure out₂

end FLT.Mazur.WeierstrassDilatation
