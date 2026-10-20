/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleTangentNeighborhoodCover

public import FLT.Mazur.WeierstrassDividedTangentOpenGluing

/-!
# Glue the actual exact-triple tangent branch outputs

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "σ" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 c
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6)

local notation "inc" => tripleTangentNeighborhoodInclusion D data hk a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "tan" => dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6

/-- Place each constructed smooth output on its actual image open. -/
def tripleTangentLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫
    tripleTangentNeighborhoodOutput D data hk a c i

/-- The complete original tangent contraction agrees on both branch opens. -/
@[reassoc] theorem tripleTangentLocalOutput_contraction (i : Bool) :
    tripleTangentLocalOutput D data hk a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (O i).ι ≫ tan := by
  simp only [tripleTangentLocalOutput, Category.assoc,
    tripleTangentNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- Glue both actual outputs in the same exact-triple finite-model smooth locus. -/
def tripleTangentGluedOutput :
    (tripleTangentBranchOutputOpen D data hk a c).toScheme ⟶
      (U).toScheme :=
  finiteTangentOpenOutput hπ data hk d a c O
    (tripleTangentLocalOutput D data hk a c)
    (tripleTangentLocalOutput_contraction D data hk a c)

/-- The glued output contracts to the original tangent formula on its entire domain. -/
@[reassoc] theorem tripleTangentGluedOutput_contraction :
    tripleTangentGluedOutput D data hk a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk =
      (tripleTangentBranchOutputOpen D data hk a c).ι ≫ tan :=
  finiteTangentOpenOutput_contraction hπ data hk d a c O _ _

/-- The glued output retains the original coefficient point. -/
@[reassoc] theorem tripleTangentGluedOutput_structure :
    tripleTangentGluedOutput D data hk a c ≫ (U).ι ≫ base =
      (tripleTangentBranchOutputOpen D data hk a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [tripleTangentGluedOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Each whole local output is recovered by the glued morphism. -/
@[reassoc] theorem tripleTangentGluedOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        tripleTangentGluedOutput D data hk a c =
      tripleTangentLocalOutput D data hk a c i :=
  finiteTangentOpenOutput_restrict hπ data hk d a c O _ _ i

/-- On an original common neighborhood, gluing recovers the actual smooth branch output. -/
@[reassoc] theorem tripleTangentGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f i ≫
        tripleTangentGluedOutput D data hk a c =
      tripleTangentNeighborhoodOutput D data hk a c i := by
  rw [tripleTangentGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
