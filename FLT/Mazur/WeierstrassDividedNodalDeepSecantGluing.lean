/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReindexedSecantOpenGluing
public import FLT.Mazur.WeierstrassDividedNodalDeepSecantNeighborhoodCover

/-!
# Glue the three actual deep-node secant outputs

The original-smooth output and both strict-branch outputs glue in the
same finite-model smooth locus. Their union covers every nodal secant
with vertical-smooth inputs when m > 4*k and k > 0. The exact original
contraction is retained on the entire union.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" =>
  (finiteGlobalStructure hπ data (k + k) hj).smoothLocus
local notation "sec" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "inc" => nodalDeepSecantNeighborhoodInclusion D data hj d a c

/-- The three concrete open domains in the original ordered secant source. -/
def nodalDeepSecantLocalOpen : Option Bool → (Spec (.of T)).Opens
  | none => finiteReindexedSmoothSecantOpen d a c
  | some i => (inc i).opensRange

local notation "O" => nodalDeepSecantLocalOpen D data hj d a c

/-- Transport the actual branch outputs onto their image opens. -/
def nodalDeepSecantLocalOutput (i : Option Bool) : (O i).toScheme ⟶ (U).toScheme :=
  match i with
  | none => finiteReindexedSmoothSecantOutput hπ data (k + k) hj d a c
  | some i => (inc i).isoOpensRange.inv ≫
      nodalDeepSecantNeighborhoodOutput D data hj d a c i

/-- Every local output contracts to the same original ordered secant. -/
@[reassoc] theorem nodalDeepSecantLocalOutput_contraction (i : Option Bool) :
    nodalDeepSecantLocalOutput D data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hj = (O i).ι ≫ sec := by
  cases i with
  | none =>
    exact finiteReindexedSmoothSecantOutput_contraction hπ
      data (k + k) hj d a c
  | some i =>
    simp only [nodalDeepSecantLocalOutput, Category.assoc,
      nodalDeepSecantNeighborhoodOutput_contraction,
      Scheme.Hom.isoOpensRange_inv_comp_assoc]
    rfl

/-- The glued family's union is exactly the previously constructed three-output open. -/
theorem nodalDeepSecantLocalOpen_union :
    (⨆ i, O i) = nodalDeepSecantOutputOpen D data hj d a c := by
  rw [iSup_option]
  rfl

/-- The three outputs glue to a single morphism into the actual resolved smooth locus. -/
def nodalDeepSecantGluedOutput : (⨆ i, O i).toScheme ⟶ (U).toScheme :=
  finiteReindexedSecantOpenOutput hπ data hj d a c O
    (nodalDeepSecantLocalOutput D data hj d a c)
    (nodalDeepSecantLocalOutput_contraction D data hj d a c)

/-- The glued output retains the complete original secant formula on the whole union. -/
@[reassoc] theorem nodalDeepSecantGluedOutput_contraction :
    nodalDeepSecantGluedOutput D data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hj = (⨆ i, O i).ι ≫ sec :=
  finiteReindexedSecantOpenOutput_contraction hπ data hj d a c O _ _

/-- Every whole local output is recovered by the glued morphism. -/
@[reassoc] theorem nodalDeepSecantGluedOutput_restrict (i : Option Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫
        nodalDeepSecantGluedOutput D data hj d a c =
      nodalDeepSecantLocalOutput D data hj d a c i :=
  finiteReindexedSecantOpenOutput_restrict hπ data hj d a c O _ _ i

/-- On an original branch neighborhood, gluing recovers its constructed smooth output. -/
@[reassoc] theorem nodalDeepSecantGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f (some i) ≫
        nodalDeepSecantGluedOutput D data hj d a c =
      nodalDeepSecantNeighborhoodOutput D data hj d a c i := by
  rw [nodalDeepSecantGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- Every classified nodal secant lies in the domain of the actual glued output. -/
theorem nodalDeepSecantGluedOutput_covers
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S T).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S T).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ ⨆ i, O i := by
  rw [nodalDeepSecantLocalOpen_union]
  exact nodalDeepSecantOutputOpen_mem D data hj d a c hk hm p hp ha hc

end FLT.Mazur.WeierstrassDividedDepth
