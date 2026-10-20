/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleSecantGluing
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# The glued triple-depth secant on two actual resolved smooth inputs

Pull the glued output domain back to the product of the same finite
model's smooth locus with itself. The resulting local addition is openly
embedded in that product and retains both inputs and the original output.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsLocalRing R] [IsNoetherianRing R] {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "T" => DividedPairSecantRing W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "p" => pullback.fst (finiteSecantInput hπ data k hk)
  (finiteResolvedPairInclusion hπ data k hk)
local notation "O" => ⨆ i, tripleSecantLocalOpen D data hk a c i

/-- Impose both actual input smoothness conditions on the glued secant output domain. -/
def tripleResolvedSecantOpen : (finiteResolvedSecantSource hπ data k hk).Opens := p ⁻¹ᵁ O

local notation "V" => tripleResolvedSecantOpen D data hk

/-- The local addition domain is a genuine open in the product of the same smooth model. -/
def tripleResolvedSecantInput : (V).toScheme ⟶ finiteResolvedProduct hπ data k hk :=
  (V).ι ≫ finiteResolvedSecantInput hπ data k hk

instance tripleResolvedSecantInput_open :
    IsOpenImmersion (tripleResolvedSecantInput D data hk) := by
  unfold tripleResolvedSecantInput
  infer_instance

/-- The smooth-input domain carries the actual glued smooth output. -/
def tripleResolvedSecantAddition : (V).toScheme ⟶ (U).toScheme :=
  (p ∣_ O) ≫ tripleSecantGluedOutput D data hk a c

/-- The complete output contracts to the original secant with the unchanged two inputs. -/
@[reassoc] theorem tripleResolvedSecantAddition_contraction :
    tripleResolvedSecantAddition D data hk ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk =
      (V).ι ≫ finiteResolvedSecantOriginalOutput hπ data k hk := by
  rw [tripleResolvedSecantAddition, Category.assoc, tripleSecantGluedOutput_contraction]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  rfl

/-- The output and both smooth inputs have the same original coefficient point. -/
@[reassoc] theorem tripleResolvedSecantAddition_structure :
    tripleResolvedSecantAddition D data hk ≫ t =
      tripleResolvedSecantInput D data hk ≫ pullback.fst t t ≫ t := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [tripleResolvedSecantAddition_contraction_assoc,
    finiteResolvedSecantOriginalOutput_structure]
  rfl

/-- The new domain retains both original resolved input projections, in their original order. -/
@[reassoc] theorem tripleResolvedSecantInput_whole :
    tripleResolvedSecantInput D data hk ≫ finiteResolvedPairInclusion hπ data k hk =
      (V).ι ≫ p ≫ finiteSecantInput hπ data k hk := by
  change (V).ι ≫ pullback.snd _ _ ≫ _ = _
  exact congrArg ((V).ι ≫ ·) pullback.condition.symm

/-- Every nodal point with vertical-smooth inputs belongs to this actual multiplication domain. -/
theorem tripleResolvedSecantOpen_mem (z : finiteResolvedSecantSource hπ data k hk)
    (hp : algebraMap R T π ∈ (p z).asIdeal)
    (ha : ((IsScalarTower.toAlgHom R (DividedPairRing W s (d).b3 (d).b4 (d).b6) T).comp a)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ (p z).asIdeal)
    (hc : ((IsScalarTower.toAlgHom R (DividedPairRing W s (d).b3 (d).b4 (d).b6) T).comp c)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ (p z).asIdeal) : z ∈ V :=
  tripleSecantGluedOutput_covers D data hk a c (p z) hp ha hc

end FLT.Mazur.WeierstrassDividedDepth
