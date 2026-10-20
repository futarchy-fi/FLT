/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantOpenGluing
public import FLT.Mazur.WeierstrassDividedTripleSecantNeighborhoodCover

/-!
# Glue the three actual triple-depth secant outputs

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
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus
local notation "sec" => dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "inc" => tripleSecantNeighborhoodInclusion D data hk a c

/-- The three concrete open domains in the original ordered secant source. -/
def tripleSecantLocalOpen : Option Bool → (Spec (.of T)).Opens
  | none => finiteSmoothSecantOpen data k hk a c
  | some i => (inc i).opensRange

local notation "O" => tripleSecantLocalOpen D data hk a c

/-- Transport the actual branch outputs onto their image opens. -/
def tripleSecantLocalOutput (i : Option Bool) : (O i).toScheme ⟶ (U).toScheme :=
  match i with
  | none => finiteSmoothSecantOutput hπ data k hk a c
  | some i => (inc i).isoOpensRange.inv ≫ tripleSecantNeighborhoodOutput D data hk a c i

/-- Every local output contracts to the same original ordered secant. -/
@[reassoc] theorem tripleSecantLocalOutput_contraction (i : Option Bool) :
    tripleSecantLocalOutput D data hk a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (O i).ι ≫ sec := by
  cases i with
  | none => exact finiteSmoothSecantOutput_contraction hπ data k hk a c
  | some i =>
    simp only [tripleSecantLocalOutput, Category.assoc,
      tripleSecantNeighborhoodOutput_contraction, Scheme.Hom.isoOpensRange_inv_comp_assoc]
    rfl

/-- The glued family's union is exactly the previously constructed three-output open. -/
theorem tripleSecantLocalOpen_union :
    (⨆ i, O i) = tripleSecantOutputOpen D data hk a c := by
  rw [iSup_option]
  rfl

/-- The three outputs glue to a single morphism into the actual resolved smooth locus. -/
def tripleSecantGluedOutput : (⨆ i, O i).toScheme ⟶ (U).toScheme :=
  finiteSecantOpenOutput hπ data hk a c O (tripleSecantLocalOutput D data hk a c)
    (tripleSecantLocalOutput_contraction D data hk a c)

/-- The glued output retains the complete original secant formula on the whole union. -/
@[reassoc] theorem tripleSecantGluedOutput_contraction :
    tripleSecantGluedOutput D data hk a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (⨆ i, O i).ι ≫ sec :=
  finiteSecantOpenOutput_contraction hπ data hk a c O _ _

/-- Every whole local output is recovered by the glued morphism. -/
@[reassoc] theorem tripleSecantGluedOutput_restrict (i : Option Bool) :
    (Scheme.Opens.iSupOpenCover O).f i ≫ tripleSecantGluedOutput D data hk a c =
      tripleSecantLocalOutput D data hk a c i :=
  finiteSecantOpenOutput_restrict hπ data hk a c O _ _ i

/-- On an original branch neighborhood, gluing recovers its constructed smooth output. -/
@[reassoc] theorem tripleSecantGluedOutput_branch (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (Scheme.Opens.iSupOpenCover O).f (some i) ≫
        tripleSecantGluedOutput D data hk a c =
      tripleSecantNeighborhoodOutput D data hk a c i := by
  rw [tripleSecantGluedOutput_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- Every classified nodal secant lies in the domain of the actual glued output. -/
theorem tripleSecantGluedOutput_covers (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S T).comp a)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S T).comp c)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal) :
    p ∈ ⨆ i, O i := by
  rw [tripleSecantLocalOpen_union]
  exact tripleSecantOutputOpen_mem D data hk a c p hp ha hc

end FLT.Mazur.WeierstrassDividedDepth
