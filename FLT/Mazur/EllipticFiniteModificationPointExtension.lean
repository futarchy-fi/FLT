/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteModificationSections
public import FLT.Mazur.ProperPointExtension

/-!
# Every original generic point extends to the actual finite modification

Properness extends the original smooth generic point, even when its original
cubic reduction is singular. Separatedness gives a unique section. Contraction
recovers the original integral cubic section, and E₀ agrees with its prior lift.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A K))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "B" => finiteGlobalSmoothEmbedding hπ data j hj

/-- Every original generic point has one integral section on the whole actual modification. -/
theorem existsUnique_finitePointSection
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ∃! t : Spec (.of A) ⟶ finiteGlobalModel hπ data j hj,
      t ≫ f = 𝟙 (Spec (.of A)) ∧ q ≫ t = projectiveToSmooth W P ≫ B := by
  let sq : ValuativeCommSq f :=
    { R := A
      K := K
      i₁ := projectiveToSmooth W P ≫ B
      i₂ := 𝟙 _
      commSq := ⟨by
        rw [Category.assoc, finiteGlobalSmoothEmbedding_structure,
          projectiveToSmooth_structure, Category.comp_id]⟩ }
  have hc : ValuativeCriterion f := by
    have hproper : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hproper
    exact hproper.1.1.1
  obtain ⟨t, ht, hs⟩ := (hc.existence sq).exists_lift
  refine ⟨t, ⟨hs, ht⟩, ?_⟩
  rintro t' ⟨hs', ht'⟩
  let _ : Subsingleton sq.commSq.LiftStruct := IsSeparated.valuativeCriterion f sq
  exact congrArg CommSq.LiftStruct.l
    (Subsingleton.elim (⟨t', ht', hs'⟩ : sq.commSq.LiftStruct) ⟨t, ht, hs⟩)

/-- The unique whole-model section of any original generic point, including outside E₀. -/
def finitePointSection (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of A) ⟶ finiteGlobalModel hπ data j hj :=
  Classical.choose (existsUnique_finitePointSection A hπ data j hj P)

/-- The constructed extension is a section of the actual finite model. -/
@[reassoc] theorem finitePointSection_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSection A hπ data j hj P ≫ f = 𝟙 (Spec (.of A)) :=
  (Classical.choose_spec (existsUnique_finitePointSection A hπ data j hj P)).1.1

/-- Generic restriction is the exact original projective point in its retained smooth chart. -/
theorem finitePointSection_generic
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    q ≫ finitePointSection A hπ data j hj P = projectiveToSmooth W P ≫ B :=
  (Classical.choose_spec (existsUnique_finitePointSection A hπ data j hj P)).1.2

/-- The original generic point determines the entire integral section. -/
theorem finitePointSection_unique
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (t : Spec (.of A) ⟶ finiteGlobalModel hπ data j hj)
    (hs : t ≫ f = 𝟙 (Spec (.of A))) (ht : q ≫ t = projectiveToSmooth W P ≫ B) :
    t = finitePointSection A hπ data j hj P :=
  (Classical.choose_spec (existsUnique_finitePointSection A hπ data j hj P)).2 t ⟨hs, ht⟩

/-- Contraction recovers the original integral section even at singular original reductions. -/
@[reassoc] theorem finitePointSection_contraction
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSection A hπ data j hj P ≫ finiteGlobalContraction hπ data j hj =
      integralPointSection A W P := by
  apply integralPointSection_unique A W P
  · exact (Category.assoc _ _ _).trans (finitePointSection_structure A hπ data j hj P)
  · rw [← Category.assoc, finitePointSection_generic, Category.assoc,
      finiteGlobalSmoothEmbedding_contraction, projectiveToSmooth_inclusion]

/-- On the original arithmetic E₀ subgroup the extension is precisely the previously built lift. -/
theorem finitePointSection_e0 (P : ellipticE0 A W) :
    finitePointSection A hπ data j hj P.val = e0FiniteSection A hπ data j hj P := by
  symm
  apply finitePointSection_unique A hπ data j hj P.val
  · exact e0FiniteSection_structure A hπ data j hj P
  · rw [e0FiniteSection, ← Category.assoc]
    exact congrArg (· ≫ B) (smoothIntegralPointSection_generic A W P.val P.property)

/-- Distinct original generic points have distinct sections of the actual modified model. -/
theorem finitePointSection_injective : Function.Injective (finitePointSection A hπ data j hj) := by
  intro P Q h
  apply integralPointSection_injective A W
  have he := congrArg (· ≫ finiteGlobalContraction hπ data j hj) h
  simpa only [finitePointSection_contraction] using he

end FLT.Mazur.WeierstrassDividedDepth
