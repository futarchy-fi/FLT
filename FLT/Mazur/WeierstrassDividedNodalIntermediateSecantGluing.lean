/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReindexedSecantOpenGluing
public import FLT.Mazur.WeierstrassDividedNodalIntermediateSecantNeighborhoodCover

/-!
# Glue the three actual intermediate-depth secant outputs

The original-smooth output and both strict-branch outputs glue in the
same finite-model smooth locus. Their union covers every nodal secant
with vertical-smooth inputs and retains the exact original contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" => (finiteGlobalStructure hπ (start := 0) data (k + r) hj).smoothLocus
local notation "sec" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "inc" => nodalIntermediateSecantNeighborhoodInclusion D hdepth hrk hrm data hj d a c

/-- The three concrete open domains in the original ordered secant source. -/
def nodalIntermediateSecantLocalOpen : Option Bool → (Spec (.of T)).Opens
  | none => finiteReindexedSmoothSecantOpen d a c
  | some i => (inc i).opensRange

local notation "O" => nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hj d a c

/-- Transport the actual branch outputs onto their image opens. -/
def nodalIntermediateSecantLocalOutput (i : Option Bool) : (O i).toScheme ⟶ (U).toScheme :=
  match i with
  | none => finiteReindexedSmoothSecantOutput hπ (start := 0) data (k + r) hj d a c
  | some i => (inc i).isoOpensRange.inv ≫
      nodalIntermediateSecantNeighborhoodOutput D hdepth hrk hrm data hj d a c i

/-- Every local output contracts to the same original ordered secant. -/
@[reassoc] theorem nodalIntermediateSecantLocalOutput_contraction (i : Option Bool) :
    nodalIntermediateSecantLocalOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj = (O i).ι ≫ sec := by
  cases i with
  | none =>
    exact finiteReindexedSmoothSecantOutput_contraction hπ (start := 0) data (k + r) hj d a c
  | some i =>
    simp only [nodalIntermediateSecantLocalOutput, Category.assoc,
      nodalIntermediateSecantNeighborhoodOutput_contraction,
      Scheme.Hom.isoOpensRange_inv_comp_assoc]
    rfl

/-- The glued family's union is exactly the previously constructed three-output open. -/
theorem nodalIntermediateSecantLocalOpen_union :
    (⨆ i, O i) = nodalIntermediateSecantOutputOpen D hdepth hrk hrm data hj d a c := by
  rw [iSup_option]
  rfl

/-- The three outputs glue to a single morphism into the actual resolved smooth locus. -/
def nodalIntermediateSecantGluedOutput : (⨆ i, O i).toScheme ⟶ (U).toScheme :=
  finiteReindexedSecantOpenOutput hπ (start := 0) data hj d a c O
    (nodalIntermediateSecantLocalOutput D hdepth hrk hrm data hj d a c)
    (nodalIntermediateSecantLocalOutput_contraction D hdepth hrk hrm data hj d a c)

/-- The glued output retains the complete original secant formula on the whole union. -/
@[reassoc] theorem nodalIntermediateSecantGluedOutput_contraction :
    nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj = (⨆ i, O i).ι ≫ sec :=
  finiteReindexedSecantOpenOutput_contraction hπ (start := 0) data hj d a c O _ _

/-- Every whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalIntermediateSecantGluedOutput_restrict (i : Option Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c =
      nodalIntermediateSecantLocalOutput D hdepth hrk hrm data hj d a c i :=
  finiteReindexedSecantOpenOutput_restrict hπ (start := 0) data hj d a c O _ _ i

/-- On an original branch neighborhood, gluing recovers its constructed smooth output. -/
@[reassoc] theorem nodalIntermediateSecantGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f (some i) ≫
        nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c =
      nodalIntermediateSecantNeighborhoodOutput D hdepth hrk hrm data hj d a c i := by
  rw [nodalIntermediateSecantGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- Every classified nodal secant lies in the domain of the actual glued output. -/
theorem nodalIntermediateSecantGluedOutput_covers
    (hk : 0 < k) (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S T).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S T).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ ⨆ i, O i := by
  rw [nodalIntermediateSecantLocalOpen_union]
  exact nodalIntermediateSecantOutputOpen_mem D hdepth hrk hrm data hj d a c hk hm hr p hp ha hc

end FLT.Mazur.WeierstrassDividedDepth
