/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReindexedSecantOpenGluing
public import FLT.Mazur.WeierstrassDividedNodalQuadrupleSecantNeighborhoodCover

/-!
# Glue the three actual quadruple-depth secant outputs

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
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" =>
  (finiteGlobalStructure hπ (splitNodeDoubledFamily D) (k + k) le_rfl).smoothLocus
local notation "sec" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "inc" => nodalQuadrupleSecantNeighborhoodInclusion D d a c

/-- The three concrete open domains in the original ordered secant source. -/
def nodalQuadrupleSecantLocalOpen : Option Bool → (Spec (.of T)).Opens
  | none => finiteReindexedSmoothSecantOpen d a c
  | some i => (inc i).opensRange

local notation "O" => nodalQuadrupleSecantLocalOpen D d a c

/-- Transport the actual branch outputs onto their image opens. -/
def nodalQuadrupleSecantLocalOutput (i : Option Bool) : (O i).toScheme ⟶ (U).toScheme :=
  match i with
  | none => finiteReindexedSmoothSecantOutput hπ (splitNodeDoubledFamily D) (k + k) le_rfl d a c
  | some i => (inc i).isoOpensRange.inv ≫
      nodalQuadrupleSecantNeighborhoodOutput D d a c i

/-- Every local output contracts to the same original ordered secant. -/
@[reassoc] theorem nodalQuadrupleSecantLocalOutput_contraction (i : Option Bool) :
    nodalQuadrupleSecantLocalOutput D d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl = (O i).ι ≫ sec := by
  cases i with
  | none =>
    exact finiteReindexedSmoothSecantOutput_contraction hπ
      (splitNodeDoubledFamily D) (k + k) le_rfl d a c
  | some i =>
    simp only [nodalQuadrupleSecantLocalOutput, Category.assoc,
      nodalQuadrupleSecantNeighborhoodOutput_contraction,
      Scheme.Hom.isoOpensRange_inv_comp_assoc]
    rfl

/-- The glued family's union is exactly the previously constructed three-output open. -/
theorem nodalQuadrupleSecantLocalOpen_union :
    (⨆ i, O i) = nodalQuadrupleSecantOutputOpen D d a c := by
  rw [iSup_option]
  rfl

/-- The three outputs glue to a single morphism into the actual resolved smooth locus. -/
def nodalQuadrupleSecantGluedOutput : (⨆ i, O i).toScheme ⟶ (U).toScheme :=
  finiteReindexedSecantOpenOutput hπ (splitNodeDoubledFamily D) le_rfl d a c O
    (nodalQuadrupleSecantLocalOutput D d a c)
    (nodalQuadrupleSecantLocalOutput_contraction D d a c)

/-- The glued output retains the complete original secant formula on the whole union. -/
@[reassoc] theorem nodalQuadrupleSecantGluedOutput_contraction :
    nodalQuadrupleSecantGluedOutput D d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl = (⨆ i, O i).ι ≫ sec :=
  finiteReindexedSecantOpenOutput_contraction hπ (splitNodeDoubledFamily D) le_rfl d a c O _ _

/-- Every whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalQuadrupleSecantGluedOutput_restrict (i : Option Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalQuadrupleSecantGluedOutput D d a c =
      nodalQuadrupleSecantLocalOutput D d a c i :=
  finiteReindexedSecantOpenOutput_restrict hπ (splitNodeDoubledFamily D) le_rfl d a c O _ _ i

/-- On an original branch neighborhood, gluing recovers its constructed smooth output. -/
@[reassoc] theorem nodalQuadrupleSecantGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f (some i) ≫
        nodalQuadrupleSecantGluedOutput D d a c =
      nodalQuadrupleSecantNeighborhoodOutput D d a c i := by
  rw [nodalQuadrupleSecantGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- Every classified nodal secant lies in the domain of the actual glued output. -/
theorem nodalQuadrupleSecantGluedOutput_covers
    (hk : 0 < k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S T).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S T).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ ⨆ i, O i := by
  rw [nodalQuadrupleSecantLocalOpen_union]
  exact nodalQuadrupleSecantOutputOpen_mem D d a c hk p hp ha hc

end FLT.Mazur.WeierstrassDividedDepth
