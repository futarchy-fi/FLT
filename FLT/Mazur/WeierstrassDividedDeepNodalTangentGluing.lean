/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepNodalTangentNeighborhoodCover

public import FLT.Mazur.WeierstrassDividedTangentOpenGluing

/-!
# Glue the actual deep-node tangent branch outputs

The complementary and swapped neighborhoods have outputs in the same
finite-model smooth locus. Flat-source uniqueness proves their agreement
on the entire overlap, so they define a single actual tangent output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  deepNodalBranchCommonOutput deepNodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "r" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

local notation "inc" => deepNodalTangentNeighborhoodInclusion D data hj d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Place each constructed smooth output on its actual image open. -/
def deepNodalTangentLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫ deepNodalTangentNeighborhoodOutput D data hj d a c i

/-- The complete original tangent contraction agrees on both branch opens. -/
@[reassoc] theorem deepNodalTangentLocalOutput_contraction (i : Bool) :
    deepNodalTangentLocalOutput D data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hj = (O i).ι ≫ tan := by
  simp only [deepNodalTangentLocalOutput, Category.assoc,
    deepNodalTangentNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- Glue both actual outputs in the same depth-2k finite-model smooth locus. -/
def deepNodalTangentGluedOutput :
    (deepNodalTangentBranchOutputOpen D data hj d a c).toScheme ⟶ (U).toScheme :=
  finiteTangentOpenOutput hπ data hj d a c O (deepNodalTangentLocalOutput D data hj d a c)
    (deepNodalTangentLocalOutput_contraction D data hj d a c)

/-- The glued output contracts to the original tangent formula on its entire domain. -/
@[reassoc] theorem deepNodalTangentGluedOutput_contraction :
    deepNodalTangentGluedOutput D data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hj =
      (deepNodalTangentBranchOutputOpen D data hj d a c).ι ≫ tan :=
  finiteTangentOpenOutput_contraction hπ data hj d a c O _ _

/-- The glued output retains the original coefficient point. -/
@[reassoc] theorem deepNodalTangentGluedOutput_structure :
    deepNodalTangentGluedOutput D data hj d a c ≫ (U).ι ≫ base =
      (deepNodalTangentBranchOutputOpen D data hj d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data (k + k) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [deepNodalTangentGluedOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Each whole local output is recovered by the glued morphism. -/
@[reassoc] theorem deepNodalTangentGluedOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫ deepNodalTangentGluedOutput D data hj d a c =
      deepNodalTangentLocalOutput D data hj d a c i :=
  finiteTangentOpenOutput_restrict hπ data hj d a c O _ _ i

/-- On an original common neighborhood, gluing recovers the actual smooth branch output. -/
@[reassoc] theorem deepNodalTangentGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f i ≫
        deepNodalTangentGluedOutput
      D data hj d a c = deepNodalTangentNeighborhoodOutput D data hj d a c i := by
  rw [deepNodalTangentGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
