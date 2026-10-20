/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNegationContraction
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.WeierstrassGlobalModificationNegationCover

/-!
# Invariant covers of all finite projective models

The complete finite local model and the unchanged invariant infinity open
cover each entire projective stage. Their constructed negatives retain the
same original integral cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "M" => finiteGlobalModel hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj

/-- The complete local chart and the actual infinity neighborhood. -/
def finiteNegationDomain (b : Bool) : Scheme :=
  if b then Spec (.of (InfinityNegationOpen W))
  else finiteModification hπ data j hj

/-- Both original domains embed into the same whole modified projective cubic. -/
def finiteNegationInclusion (b : Bool) : finiteNegationDomain hπ data j hj b ⟶ M :=
  match b with
  | false => finiteLocalChart hπ data j hj
  | true => infinityNegationInclusion W ≫ finiteInfinityChart hπ data j hj

instance finiteNegationInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (finiteNegationInclusion hπ data j hj b) := by
  cases b <;> dsimp [finiteNegationInclusion] <;> infer_instance

/-- The invariant local and infinity domains cover every point of the whole model. -/
theorem finiteNegationInclusion_covers (z : M) :
    ∃ b, ∃ y, finiteNegationInclusion hπ data j hj b y = z := by
  rcases finiteGlobal_charts_cover hπ data j hj z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨b, t, ht⟩ := (negationYCover W).exists_eq y
    cases b
    · let _ : IsIso (chartTransition W 2 1) :=
        inferInstanceAs (IsIso ((integralCurveGlueData W).t ⟨2⟩ ⟨1⟩))
      refine ⟨false, (inv (chartTransition W 2 1) ≫
        finiteYBoundary hπ data j hj) t, ?_⟩
      have he : (inv (chartTransition W 2 1) ≫ finiteYBoundary hπ data j hj) ≫
          finiteLocalChart hπ data j hj =
          overlapInclusion W 1 2 ≫ finiteInfinityChart hπ data j hj := by
        rw [Category.assoc]
        change inv _ ≫ (_ ≫ pushout.inr _ _) = _ ≫ pushout.inl _ _
        rw [← pushout.condition]
        change inv (chartTransition W 2 1) ≫
          (chartTransition W 2 1 ≫ overlapInclusion W 1 2) ≫ _ = _
        rw [Category.assoc, IsIso.inv_hom_id_assoc]
      change ((inv (chartTransition W 2 1) ≫ finiteYBoundary hπ data j hj) ≫
        finiteLocalChart hπ data j hj) t = _
      rw [he]
      exact congrArg (finiteInfinityChart hπ data j hj) ht
    · exact ⟨true, t, congrArg (finiteInfinityChart hπ data j hj) ht⟩
  · exact ⟨false, y, rfl⟩

/-- The actual invariant two-domain cover of the complete projective modification. -/
def finiteNegationCover : (M).OpenCover where
  I₀ := Bool
  X := finiteNegationDomain hπ data j hj
  f := finiteNegationInclusion hπ data j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨finiteNegationInclusion_covers hπ data j hj,
      fun b => finiteNegationInclusion_isOpenImmersion hπ data j hj b⟩

/-- The constructed negative on each complete invariant domain. -/
def finiteNegationDomainIso (b : Bool) :
    finiteNegationDomain hπ data j hj b ≅ finiteNegationDomain hπ data j hj b :=
  match b with
  | false => finiteWholeNegationIso hπ data j hj
  | true => WeierstrassGlobalModification.infinityNegationIso W

/-- Both actual domain negatives retain the original projective cubic map. -/
@[reassoc] theorem finiteNegationDomainIso_contraction (b : Bool) :
    (finiteNegationDomainIso hπ data j hj b).hom ≫
        finiteNegationInclusion hπ data j hj b ≫ c =
      finiteNegationInclusion hπ data j hj b ≫ c ≫ integralCurveNegation W := by
  cases b
  · change (finiteWholeNegationIso hπ data j hj).hom ≫
      finiteLocalChart hπ data j hj ≫ c = finiteLocalChart hπ data j hj ≫ c ≫ _
    rw [finiteLocalChart_contraction, finiteLocalChart_contraction_assoc,
      finiteWholeNegationIso_toCurve]
  · change Spec.map (CommRingCat.ofHom (infinityNegationEnd W).toRingHom) ≫
        (infinityNegationInclusion W ≫ finiteInfinityChart hπ data j hj) ≫ c =
      (infinityNegationInclusion W ≫ finiteInfinityChart hπ data j hj) ≫ c ≫ _
    simp only [Category.assoc, finiteInfinityChart_contraction,
      finiteInfinityChart_contraction_assoc]
    rw [← Category.assoc, infinityNegationEnd_spec_restriction,
      integralCurveChart_negation_infinity]

end FLT.Mazur.WeierstrassDividedDepth
