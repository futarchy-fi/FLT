/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Promote the actual exact-triple law to a common later finite model

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
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "V" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "Os" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "ft" => tripleTangentGluedOutput D data hk a c
local notation "fs" => tripleSecantGluedOutput D data hk a c

variable (q : ℕ) (hq : q ≤ n) (hrq : k ≤ q)
local notation "target" => finiteGlobalStructure hπ data q hq
local notation "Q" => (target).smoothLocus
local notation "O" => tripleAdditionOpen D data hk a c
local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "out" => tripleAdditionOutput D data hk a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data k q hrq hq

/-- The constructed exact-triple law with its whole output in a common later smooth model. -/
def triplePromotedAddition : (O).toScheme ⟶ (Q).toScheme :=
  tripleAddition D data hk a c ≫ promote

/-- Each entire local formula is preserved, with only its actual target stage promoted. -/
@[reassoc] theorem triplePromotedAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        triplePromotedAddition D data hk a c q hq hrq =
      out i ≫ promote := by
  rw [triplePromotedAddition, tripleAddition_formula_assoc]

/-- Promotion preserves the full original cubic output on the entire glued domain. -/
@[reassoc] theorem triplePromotedAddition_contraction :
    triplePromotedAddition D data hk a c q hq hrq ≫ (Q).ι ≫
        finiteGlobalContraction hπ data q hq =
      tripleAddition D data hk a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk := by
  rw [triplePromotedAddition, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- The promoted law retains the exact original coefficient map on its whole domain. -/
@[reassoc] theorem triplePromotedAddition_structure :
    triplePromotedAddition D data hk a c q hq hrq ≫ (Q).ι ≫ target =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [triplePromotedAddition, Category.assoc, finiteGlobalSmoothTransition_structure,
    tripleAddition_structure]

/-- On the tangent domain the promoted law is still the actual original tangent formula. -/
@[reassoc] theorem triplePromotedAddition_tangent_contraction :
    (inc true).isoOpensRange.hom ≫ (C).f true ≫
        triplePromotedAddition D data hk a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Ot).ι ≫ dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  rw [triplePromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact tripleTangentGluedOutput_contraction D data hk a c

/-- On the secant domain the promoted law is still the actual original secant formula. -/
@[reassoc] theorem triplePromotedAddition_secant_contraction :
    (inc false).isoOpensRange.hom ≫ (C).f false ≫
        triplePromotedAddition D data hk a c q hq hrq ≫ (Q).ι ≫
          finiteGlobalContraction hπ data q hq =
      (Os).ι ≫ dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  rw [triplePromotedAddition_formula_assoc, finiteGlobalSmoothTransition_contraction]
  exact tripleSecantGluedOutput_contraction D data hk a c

end FLT.Mazur.WeierstrassDividedDepth
