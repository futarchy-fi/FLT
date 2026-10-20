/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowTangentNeighborhoodCover

public import FLT.Mazur.WeierstrassDividedTangentOpenGluing

/-!
# Glue the actual shallow-depth tangent branch outputs

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
  nodalShallowBranchCommonOutput nodalShallowNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

local notation "inc" => nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Place each constructed smooth output on its actual image open. -/
def nodalShallowTangentLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫
    nodalShallowTangentNeighborhoodOutput D hdepth hm data hj d a c i

/-- The complete original tangent contraction agrees on both branch opens. -/
@[reassoc] theorem nodalShallowTangentLocalOutput_contraction (i : Bool) :
    nodalShallowTangentLocalOutput D hdepth hm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj = (O i).ι ≫ tan := by
  simp only [nodalShallowTangentLocalOutput, Category.assoc,
    nodalShallowTangentNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- Glue both actual outputs in the same shallow-depth finite-model smooth locus. -/
def nodalShallowTangentGluedOutput :
    (nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c).toScheme ⟶
      (U).toScheme :=
  finiteTangentOpenOutput hπ (start := 0) data hj d a c O
    (nodalShallowTangentLocalOutput D hdepth hm data hj d a c)
    (nodalShallowTangentLocalOutput_contraction D hdepth hm data hj d a c)

/-- The glued output contracts to the original tangent formula on its entire domain. -/
@[reassoc] theorem nodalShallowTangentGluedOutput_contraction :
    nodalShallowTangentGluedOutput D hdepth hm data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      (nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c).ι ≫ tan :=
  finiteTangentOpenOutput_contraction hπ (start := 0) data hj d a c O _ _

/-- The glued output retains the original coefficient point. -/
@[reassoc] theorem nodalShallowTangentGluedOutput_structure :
    nodalShallowTangentGluedOutput D hdepth hm data hj d a c ≫ (U).ι ≫ base =
      (nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalShallowTangentGluedOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Each whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalShallowTangentGluedOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalShallowTangentGluedOutput D hdepth hm data hj d a c =
      nodalShallowTangentLocalOutput D hdepth hm data hj d a c i :=
  finiteTangentOpenOutput_restrict hπ (start := 0) data hj d a c O _ _ i

/-- On an original common neighborhood, gluing recovers the actual smooth branch output. -/
@[reassoc] theorem nodalShallowTangentGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalShallowTangentGluedOutput D hdepth hm data hj d a c =
      nodalShallowTangentNeighborhoodOutput D hdepth hm data hj d a c i := by
  rw [nodalShallowTangentGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
