/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Embed every relatively smooth divided input at a common finite stage

The source is the full relative smooth open of the actual divided equation.
No vertical-derivative condition is imposed. Its original chart map and cubic
contraction survive promotion to any supplied later finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (i : ℕ) (hi : i ≤ n)
local notation "d" => data ⟨i, Nat.lt_succ_of_le hi⟩
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + i))
  (d).b3 (d).b4 (d).b6
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "base" => finiteGlobalStructure hπ data i hi
local notation "U" => (base).smoothLocus
local notation "c" => finiteSecantDividedChart hπ data i hi

/-- Every relatively smooth divided-chart point is smooth in its actual finite model. -/
theorem finiteDividedSmoothChart_range : Set.range ((V).ι ≫ c) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq c base
  simp only [finiteSecantDividedChart_structure] at h
  exact h.ge p.property

/-- The entire divided relative smooth locus embeds in the corresponding finite smooth model. -/
def finiteDividedSmoothChart : (V).toScheme ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι ((V).ι ≫ c) (by
    rw [Scheme.Opens.range_ι]
    exact finiteDividedSmoothChart_range hπ data i hi)

instance finiteDividedSmoothChart_open :
    IsOpenImmersion (finiteDividedSmoothChart hπ data i hi) := by
  unfold finiteDividedSmoothChart
  infer_instance

/-- The complete smooth chart retains the original divided chart embedding. -/
@[reassoc] theorem finiteDividedSmoothChart_inclusion :
    finiteDividedSmoothChart hπ data i hi ≫ (U).ι = (V).ι ≫ c :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its original cubic contraction is unchanged on the entire divided smooth locus. -/
@[reassoc] theorem finiteDividedSmoothChart_contraction :
    finiteDividedSmoothChart hπ data i hi ≫ (U).ι ≫
        finiteGlobalContraction hπ data i hi = (V).ι ≫ toCurve d := by
  rw [finiteDividedSmoothChart_inclusion_assoc, finiteSecantDividedChart_contraction]

/-- The complete smooth divided chart retains its coefficient morphism. -/
@[reassoc] theorem finiteDividedSmoothChart_structure :
    finiteDividedSmoothChart hπ data i hi ≫ (U).ι ≫ base = (V).ι ≫ s := by
  rw [finiteDividedSmoothChart_inclusion_assoc, finiteSecantDividedChart_structure]

variable (j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "next" => finiteGlobalStructure hπ data j hj
local notation "Q" => (next).smoothLocus

/-- Promote the entire actual divided smooth chart into a supplied common finite stage. -/
def finitePromotedDividedSmoothChart : (V).toScheme ⟶ (Q).toScheme :=
  finiteDividedSmoothChart hπ data i hi ≫ finiteGlobalSmoothTransition hπ data i j hij hj

instance finitePromotedDividedSmoothChart_open :
    IsOpenImmersion (finitePromotedDividedSmoothChart hπ data i hi j hij hj) := by
  unfold finitePromotedDividedSmoothChart
  infer_instance

/-- Promotion preserves the full original cubic input, including exceptional smooth points. -/
@[reassoc] theorem finitePromotedDividedSmoothChart_contraction :
    finitePromotedDividedSmoothChart hπ data i hi j hij hj ≫ (Q).ι ≫
        finiteGlobalContraction hπ data j hj = (V).ι ≫ toCurve d := by
  rw [finitePromotedDividedSmoothChart, Category.assoc,
    finiteGlobalSmoothTransition_contraction, finiteDividedSmoothChart_contraction]

/-- Every promoted smooth input retains its original coefficient point. -/
@[reassoc] theorem finitePromotedDividedSmoothChart_structure :
    finitePromotedDividedSmoothChart hπ data i hi j hij hj ≫ (Q).ι ≫ next = (V).ι ≫ s := by
  rw [finitePromotedDividedSmoothChart, Category.assoc,
    finiteGlobalSmoothTransition_structure, finiteDividedSmoothChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
