/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorActionAtlas
public import FLT.Mazur.WeierstrassDividedFiniteChartStructure
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior

/-!
# Refining every retained input by its actual finite exterior charts

The whole retained-input branch is covered by its original x chart and
all preceding successive x charts. Pullback and affine refinement retain
flat projections to those actual equation charts, including special fibers.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)

/-- The actual original and successive x charts cover the entire preceding exterior. -/
def finitePrecedingExteriorOpenCover : (E).carrier.OpenCover where
  I₀ := Fin (j + 1)
  X := finiteExteriorAtlasObject data E₀ j (Nat.le_of_succ_le hj)
  f := finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨finiteExteriorAtlas_cover hπ data E₀ j (Nat.le_of_succ_le hj),
      fun _ => inferInstance⟩

variable (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
  finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
local notation "D" => successorDividedInputCover hπ data j hj a

/-- The full retained-input domain over the normalized output chart. -/
abbrev successorRetainedInputDomain := (D).X (some none)

/-- Its actual projection to the recursively enlarged preceding exterior. -/
def successorRetainedInputProjection : successorRetainedInputDomain hπ data j hj a ⟶
    (E).carrier := pullback.snd _ _

instance successorRetainedInputProjection_flat :
    Flat (successorRetainedInputProjection hπ data j hj a) := by
  unfold successorRetainedInputProjection
  infer_instance

/-- Pull back every original and successive exterior input chart. -/
def successorRetainedInputCover : (successorRetainedInputDomain hπ data j hj a).OpenCover :=
  (finitePrecedingExteriorOpenCover hπ data j hj).pullback₁
    (successorRetainedInputProjection hπ data j hj a)

/-- A complete affine atlas of the full retained-input branch. -/
def successorRetainedAffineCover :
    (successorRetainedInputDomain hπ data j hj a).AffineOpenCover :=
  (successorRetainedInputCover hπ data j hj a).affineRefinement

/-- Each refined member retains the actual exterior equation chart it came from. -/
def successorRetainedChartProjection (i : (successorRetainedAffineCover hπ data j hj a).I₀) :
    Spec ((successorRetainedAffineCover hπ data j hj a).X i) ⟶
      finiteExteriorAtlasObject data E₀ j (Nat.le_of_succ_le hj) i.1 :=
  ((successorRetainedInputCover hπ data j hj a).X i.1).affineCover.f i.2 ≫ pullback.snd _ _

/-- Regular equation-chart generators stay regular on these actual flat projections. -/
instance successorRetainedChartProjection_flat
    (i : (successorRetainedAffineCover hπ data j hj a).I₀) :
    Flat (successorRetainedChartProjection hπ data j hj a i) := by
  unfold successorRetainedChartProjection
  infer_instance

/-- The refined chart projection preserves the entire retained input. -/
@[reassoc] theorem successorRetainedChartProjection_input
    (i : (successorRetainedAffineCover hπ data j hj a).I₀) :
    successorRetainedChartProjection hπ data j hj a i ≫
        finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i.1 =
      (successorRetainedAffineCover hπ data j hj a).f i ≫
        successorRetainedInputProjection hπ data j hj a := by
  exact (Category.assoc _ _ _).trans
    ((congrArg
      (fun t => ((successorRetainedInputCover hπ data j hj a).X i.1).affineCover.f i.2 ≫ t)
      (pullback.condition (f := successorRetainedInputProjection hπ data j hj a)
        (g := (finitePrecedingExteriorOpenCover hπ data j hj).f i.1)).symm).trans
          (Category.assoc _ _ _).symm)

/-- No point of the full retained-input branch is omitted by the refinement. -/
theorem successorRetainedAffineCover_covers (z : successorRetainedInputDomain hπ data j hj a) :
    ∃ i x, (successorRetainedAffineCover hπ data j hj a).f i x = z :=
  (successorRetainedAffineCover hπ data j hj a).openCover.exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
