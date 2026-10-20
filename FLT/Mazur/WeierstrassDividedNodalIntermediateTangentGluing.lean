/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateTangentNeighborhoodCover

public import FLT.Mazur.WeierstrassDividedTangentOpenGluing

/-!
# Glue the actual intermediate-depth tangent branch outputs

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
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

local notation "inc" => nodalIntermediateTangentNeighborhoodInclusion D hdepth hrk hrm data hj d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Place each constructed smooth output on its actual image open. -/
def nodalIntermediateTangentLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫
    nodalIntermediateTangentNeighborhoodOutput D hdepth hrk hrm data hj d a c i

/-- The complete original tangent contraction agrees on both branch opens. -/
@[reassoc] theorem nodalIntermediateTangentLocalOutput_contraction (i : Bool) :
    nodalIntermediateTangentLocalOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj = (O i).ι ≫ tan := by
  simp only [nodalIntermediateTangentLocalOutput, Category.assoc,
    nodalIntermediateTangentNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- Glue both actual outputs in the same intermediate-depth finite-model smooth locus. -/
def nodalIntermediateTangentGluedOutput :
    (nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c).toScheme ⟶
      (U).toScheme :=
  finiteTangentOpenOutput hπ (start := 0) data hj d a c O
    (nodalIntermediateTangentLocalOutput D hdepth hrk hrm data hj d a c)
    (nodalIntermediateTangentLocalOutput_contraction D hdepth hrk hrm data hj d a c)

/-- The glued output contracts to the original tangent formula on its entire domain. -/
@[reassoc] theorem nodalIntermediateTangentGluedOutput_contraction :
    nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      (nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c).ι ≫ tan :=
  finiteTangentOpenOutput_contraction hπ (start := 0) data hj d a c O _ _

/-- The glued output retains the original coefficient point. -/
@[reassoc] theorem nodalIntermediateTangentGluedOutput_structure :
    nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c ≫ (U).ι ≫ base =
      (nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (k + r) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalIntermediateTangentGluedOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Each whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalIntermediateTangentGluedOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c =
      nodalIntermediateTangentLocalOutput D hdepth hrk hrm data hj d a c i :=
  finiteTangentOpenOutput_restrict hπ (start := 0) data hj d a c O _ _ i

/-- On an original common neighborhood, gluing recovers the actual smooth branch output. -/
@[reassoc] theorem nodalIntermediateTangentGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c =
      nodalIntermediateTangentNeighborhoodOutput D hdepth hrk hrm data hj d a c i := by
  rw [nodalIntermediateTangentGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
