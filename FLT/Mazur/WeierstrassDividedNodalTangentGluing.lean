/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalTangentNeighborhoodCover

public import FLT.Mazur.WeierstrassDividedTangentOpenGluing

/-!
# Glue the actual quadruple-depth tangent branch outputs

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
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "data" => splitNodeDoubledFamily D
local notation "s" => π ^ k
local notation "r" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) le_rfl
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

local notation "inc" => nodalTangentNeighborhoodInclusion D d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Place each constructed smooth output on its actual image open. -/
def nodalTangentLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫ nodalTangentNeighborhoodOutput D d a c i

/-- The complete original tangent contraction agrees on both branch opens. -/
@[reassoc] theorem nodalTangentLocalOutput_contraction (i : Bool) :
    nodalTangentLocalOutput D d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) le_rfl = (O i).ι ≫ tan := by
  simp only [nodalTangentLocalOutput, Category.assoc,
    nodalTangentNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- Glue both actual outputs in the same depth-2k finite-model smooth locus. -/
def nodalTangentGluedOutput :
    (nodalTangentBranchOutputOpen D d a c).toScheme ⟶ (U).toScheme :=
  finiteTangentOpenOutput hπ data le_rfl d a c O (nodalTangentLocalOutput D d a c)
    (nodalTangentLocalOutput_contraction D d a c)

/-- The glued output contracts to the original tangent formula on its entire domain. -/
@[reassoc] theorem nodalTangentGluedOutput_contraction :
    nodalTangentGluedOutput D d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) le_rfl =
      (nodalTangentBranchOutputOpen D d a c).ι ≫ tan :=
  finiteTangentOpenOutput_contraction hπ data le_rfl d a c O _ _

/-- The glued output retains the original coefficient point. -/
@[reassoc] theorem nodalTangentGluedOutput_structure :
    nodalTangentGluedOutput D d a c ≫ (U).ι ≫ base =
      (nodalTangentBranchOutputOpen D d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data (k + k) le_rfl ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalTangentGluedOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Each whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalTangentGluedOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫ nodalTangentGluedOutput D d a c =
      nodalTangentLocalOutput D d a c i :=
  finiteTangentOpenOutput_restrict hπ data le_rfl d a c O _ _ i

/-- On an original common neighborhood, gluing recovers the actual smooth branch output. -/
@[reassoc] theorem nodalTangentGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalTangentGluedOutput D d a c = nodalTangentNeighborhoodOutput D d a c i := by
  rw [nodalTangentGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
