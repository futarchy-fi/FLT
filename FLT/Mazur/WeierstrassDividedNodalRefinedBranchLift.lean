/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchOutput
public import FLT.Mazur.WeierstrassDividedDepthMaps
public import FLT.Mazur.WeierstrassDividedTangentBranchScheme

/-!
# Intermediate nodal branch morphisms with their original contraction

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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k r : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k) (e : Data W π (k + r))
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S) [Module.Flat R S]
local notation "s" => π ^ k
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "b4'" => nodalBranchFourth D d hdepth
local notation "b6'" => nodalBranchConstant D d hdepth
local notation "h4'" => nodalBranchFourth_factor D d hdepth
local notation "h6'" => nodalBranchConstant_factor D d hdepth
local notation "hs" => isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ)
local notation "old" => dividedTangentBranchLift W s d.b3 d.b4 d.b6 a c
  a2 b4' b6' hs h2 d.factor3 d.factor4 d.factor6 h4' h6'
local notation "res" => dividedTangentBranchRestriction W s d.b3 d.b4 d.b6 a c
local notation "out" => nodalRefinedBranchOutput D d hdepth hrk hrm e a2 h2 a c
/-- The constructed morphism into the actual available deeper chart. -/
def nodalRefinedBranchLift : Spec (.of B) ⟶ chart e :=
  Spec.map (CommRingCat.ofHom (out).toRingHom)

/-- Its actual depth transition is the complete previously constructed output. -/
@[reassoc] theorem nodalRefinedBranchLift_transition :
    nodalRefinedBranchLift D d hdepth hrk hrm e a2 h2 a c ≫
      depthMap hπ d e (show k ≤ k + r by omega) = old := by
  rw [nodalRefinedBranchLift, depthMap, depthTransitionMorphism, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((out).comp
    (depthTransition π k (k + r) hπ (show k ≤ k + r by omega) W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
      d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)).toRingHom) = _
  rw [nodalRefinedBranchOutput_transition]
  rfl

/-- The available-depth output contracts to exactly the original tangent sum. -/
@[reassoc] theorem nodalRefinedBranchLift_contraction :
    nodalRefinedBranchLift D d hdepth hrk hrm e a2 h2 a c ≫ toCurve e =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [← depthMap_toCurve hπ d e (show k ≤ k + r by omega), nodalRefinedBranchLift_transition_assoc]
  exact dividedTangentBranchLift_contraction ..

/-- The output retains the original coefficient map of the full branch source. -/
@[reassoc] theorem nodalRefinedBranchLift_structure :
    nodalRefinedBranchLift D d hdepth hrk hrm e a2 h2 a c ≫
      Spec.map (CommRingCat.ofHom (algebraMap R
        (Coordinate W (π ^ (k + r)) e.b3 e.b4 e.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
