/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalDeepAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Promote the actual deep-node law to a common later finite model

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
  deepNodalBranchCommonOutput deepNodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "V" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hkk
local notation "U" => (base).smoothLocus
local notation "Ot" => deepNodalTangentBranchOutputOpen D data hkk d a c
local notation "Os" => ⨆ i, nodalDeepSecantLocalOpen D data hkk d a c i
local notation "ft" => deepNodalTangentGluedOutput D data hkk d a c
local notation "fs" => nodalDeepSecantGluedOutput D data hkk d a c

variable (q : ℕ) (hq : q ≤ n) (hrq : k + k ≤ q)
local notation "target" => finiteGlobalStructure hπ data q hq
local notation "Q" => (target).smoothLocus
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "inc" => nodalDeepAdditionInclusion D data hkk d a c
local notation "out" => nodalDeepAdditionOutput D data hkk d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + k) q hrq hq

/-- The constructed deep-node law with its whole output in a common later smooth model. -/
def deepPromotedAddition : (O).toScheme ⟶ (Q).toScheme :=
  nodalDeepAddition D data hkk d a c ≫ promote

/-- Each entire local formula is preserved, with only its actual target stage promoted. -/
@[reassoc] theorem deepPromotedAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        deepPromotedAddition D data hkk d a c q hq hrq =
      out i ≫ promote := by
  rw [deepPromotedAddition, nodalDeepAddition_formula_assoc]

/-- Promotion preserves the full original cubic output on the entire glued domain. -/
@[reassoc] theorem deepPromotedAddition_contraction :
    deepPromotedAddition D data hkk d a c q hq hrq ≫ (Q).ι ≫
        finiteGlobalContraction hπ data q hq =
      nodalDeepAddition D data hkk d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hkk := by
  rw [deepPromotedAddition, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- The promoted law retains the exact original coefficient map on its whole domain. -/
@[reassoc] theorem deepPromotedAddition_structure :
    deepPromotedAddition D data hkk d a c q hq hrq ≫ (Q).ι ≫ target =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [deepPromotedAddition, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalDeepAddition_structure]

/-- On the tangent domain the promoted law is still the actual original tangent formula. -/
@[reassoc] theorem deepPromotedAddition_tangent_contraction :
    (inc true).isoOpensRange.hom ≫ (C).f true ≫
        deepPromotedAddition D data hkk d a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Ot).ι ≫ dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  rw [deepPromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact deepNodalTangentGluedOutput_contraction D data hkk d a c

/-- On the secant domain the promoted law is still the actual original secant formula. -/
@[reassoc] theorem deepPromotedAddition_secant_contraction :
    (inc false).isoOpensRange.hom ≫ (C).f false ≫
        deepPromotedAddition D data hkk d a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Os).ι ≫ dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  rw [deepPromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact nodalDeepSecantGluedOutput_contraction D data hkk d a c

end FLT.Mazur.WeierstrassDividedDepth
