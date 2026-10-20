/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Promote the actual intermediate law to a common later finite model

The entire constructed output moves through unchanged smooth opens. Its source,
local formulas, original cubic contractions and coefficient structure are retained.
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
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c
local notation "Os" => ⨆ i, nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hj d a c i
local notation "ft" => nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c
local notation "fs" => nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c

variable (q : ℕ) (hq : q ≤ n) (hrq : k + r ≤ q)
local notation "target" => finiteGlobalStructure hπ (start := 0) data q hq
local notation "Q" => (target).smoothLocus
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hj d a c
local notation "inc" => nodalIntermediateAdditionInclusion D hdepth hrk hrm data hj d a c
local notation "out" => nodalIntermediateAdditionOutput D hdepth hrk hrm data hj d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + r) q hrq hq

/-- The constructed intermediate law with its whole output in a common later smooth model. -/
def nodalIntermediatePromotedAddition : (O).toScheme ⟶ (Q).toScheme :=
  nodalIntermediateAddition D hdepth hrk hrm data hj d a c ≫ promote

/-- Each entire local formula is preserved, with only its actual target stage promoted. -/
@[reassoc] theorem nodalIntermediatePromotedAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        nodalIntermediatePromotedAddition D hdepth hrk hrm data hj d a c q hq hrq =
      out i ≫ promote := by
  rw [nodalIntermediatePromotedAddition, nodalIntermediateAddition_formula_assoc]

/-- Promotion preserves the full original cubic output on the entire glued domain. -/
@[reassoc] theorem nodalIntermediatePromotedAddition_contraction :
    nodalIntermediatePromotedAddition D hdepth hrk hrm data hj d a c q hq hrq ≫ (Q).ι ≫
        finiteGlobalContraction hπ data q hq =
      nodalIntermediateAddition D hdepth hrk hrm data hj d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + r) hj := by
  rw [nodalIntermediatePromotedAddition, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- The promoted law retains the exact original coefficient map on its whole domain. -/
@[reassoc] theorem nodalIntermediatePromotedAddition_structure :
    nodalIntermediatePromotedAddition D hdepth hrk hrm data hj d a c q hq hrq ≫ (Q).ι ≫ target =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalIntermediatePromotedAddition, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalIntermediateAddition_structure]

/-- On the tangent domain the promoted law is still the actual original tangent formula. -/
@[reassoc] theorem nodalIntermediatePromotedAddition_tangent_contraction :
    (inc true).isoOpensRange.hom ≫ (C).f true ≫
        nodalIntermediatePromotedAddition D hdepth hrk hrm data hj d a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Ot).ι ≫ dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  rw [nodalIntermediatePromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact nodalIntermediateTangentGluedOutput_contraction D hdepth hrk hrm data hj d a c

/-- On the secant domain the promoted law is still the actual original secant formula. -/
@[reassoc] theorem nodalIntermediatePromotedAddition_secant_contraction :
    (inc false).isoOpensRange.hom ≫ (C).f false ≫
        nodalIntermediatePromotedAddition D hdepth hrk hrm data hj d a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Os).ι ≫ dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  rw [nodalIntermediatePromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact nodalIntermediateSecantGluedOutput_contraction D hdepth hrk hrm data hj d a c

end FLT.Mazur.WeierstrassDividedDepth
