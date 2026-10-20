/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBranchOutput
public import FLT.Mazur.WeierstrassDividedDepthMaps
public import FLT.Mazur.WeierstrassDividedTangentBranchScheme

/-!
# The deeper branch morphism in an available depth chart

The constructed output refines the entire older branch output. Consequently
its original cubic contraction and coefficient point are unchanged.
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
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hl : l = k + k)
  (h2 : W.a₂ = 0)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S) [Module.Flat R S]
local notation "s" => π ^ k
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "h4'" => branch_available_factor4 hπ d e hl
local notation "h6'" => branch_available_factor6 hπ d e hl
local notation "h2'" => branch_normalized_factor2 (π := π) (k := k) h2
local notation "hs" => isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ)
local notation "old" => dividedTangentBranchLift W s d.b3 d.b4 d.b6 a c
  0 e.b4 (s * e.b6) hs h2' d.factor3 d.factor4 d.factor6 h4' h6'
local notation "r" => dividedTangentBranchRestriction W s d.b3 d.b4 d.b6 a c

/-- The constructed morphism into the actual available deeper chart. -/
def depthBranchLift : Spec (.of B) ⟶ chart e :=
  Spec.map (CommRingCat.ofHom (depthBranchOutput hπ d e hl h2 a c).toRingHom)

/-- Its actual depth transition is the complete previously constructed output. -/
@[reassoc] theorem depthBranchLift_transition (hkl : k ≤ l) :
    depthBranchLift hπ d e hl h2 a c ≫ depthMap hπ d e hkl = old := by
  rw [depthBranchLift, depthMap, depthTransitionMorphism, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((depthBranchOutput hπ d e hl h2 a c).comp
    (depthTransition π k l hπ hkl W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
      d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)).toRingHom) = _
  rw [depthBranchOutput_transition]
  rfl

/-- The available-depth output contracts to exactly the original tangent sum. -/
@[reassoc] theorem depthBranchLift_contraction :
    depthBranchLift hπ d e hl h2 a c ≫ toCurve e =
      Spec.map (CommRingCat.ofHom (r).toRingHom) ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  have hkl : k ≤ l := by omega
  rw [← depthMap_toCurve hπ d e hkl, depthBranchLift_transition_assoc]
  exact dividedTangentBranchLift_contraction ..

/-- The output retains the original coefficient map of the full branch source. -/
@[reassoc] theorem depthBranchLift_structure :
    depthBranchLift hπ d e hl h2 a c ≫
      Spec.map (CommRingCat.ofHom (algebraMap R
        (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
