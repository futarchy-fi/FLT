/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedQuotientPresheaf

/-!
# The universal property of the full unmarked parameter quotient

The actual quotient projection is pointwise surjective. Every natural map
constant on genuine compatible comparisons factors uniquely through it.
The target can be any presheaf; no sheaf or representability assumption is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]

/-- Forget the parameter while retaining its full unmarked equivalence class. -/
def unmarkedParameterProjection :
    normalizedParameterPresheaf n ⟶ unmarkedParameterClassPresheaf n where
  app _ := ↾(Quotient.mk _)
  naturality _ _ _ := rfl

/-- Every pointwise unmarked class has an actual parameter representative. -/
theorem unmarkedParameterProjection_surjective (T : Schemeᵒᵖ) :
    Function.Surjective ((unmarkedParameterProjection n).app T) :=
  Quotient.mk_surjective

/-- Its pointwise kernel is the original full compatible comparison relation. -/
theorem unmarkedParameterProjection_eq_iff {T : Scheme} (q r : NormalizedParameter n T) :
    (unmarkedParameterProjection n).app (Opposite.op T) q =
      (unmarkedParameterProjection n).app (Opposite.op T) r ↔
        (normalizedParameterSetoid n T).r q r :=
  Quotient.eq

/-- Projection followed by forgetting is the original parameter-to-moduli map. -/
theorem unmarkedParameterProjection_moduli :
    unmarkedParameterProjection n ≫ unmarkedParameterModuliMap n =
      normalizedParameterModuliMap n := rfl

variable {F : Schemeᵒᵖ ⥤ Type 1} (v : normalizedParameterPresheaf n ⟶ F)

/-- A presheaf-valued invariant identifies all original full compatible comparisons. -/
def ParameterInvariant : Prop :=
  ∀ (T : Scheme) (q r : NormalizedParameter n T),
    (normalizedParameterSetoid n T).r q r →
      v.app (Opposite.op T) q = v.app (Opposite.op T) r

variable (hv : ParameterInvariant n v)

/-- Descend an actual invariant to full unmarked parameter classes. -/
def unmarkedParameterDesc : unmarkedParameterClassPresheaf n ⟶ F where
  app T := ↾(Quotient.lift (v.app T) (hv T.unop))
  naturality T U g := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      exact congrArg (fun k ↦ k q) (v.naturality g)

/-- Descent retains the value on every original parameter. -/
@[reassoc] theorem unmarkedParameterProjection_desc :
    unmarkedParameterProjection n ≫ unmarkedParameterDesc n v hv = v := rfl

/-- Natural maps out of the quotient are determined by all actual parameters. -/
theorem unmarkedParameter_hom_ext
    {a b : unmarkedParameterClassPresheaf n ⟶ F}
    (h : unmarkedParameterProjection n ≫ a = unmarkedParameterProjection n ≫ b) : a = b := by
  ext T z
  obtain ⟨q, rfl⟩ := unmarkedParameterProjection_surjective n T z
  exact congrArg (fun k ↦ k.app T q) h

include hv in
/-- The full unmarked quotient has the expected unique factorization property. -/
theorem unmarkedParameter_desc_existsUnique :
    ∃! d : unmarkedParameterClassPresheaf n ⟶ F,
      unmarkedParameterProjection n ≫ d = v := by
  refine ⟨unmarkedParameterDesc n v hv, unmarkedParameterProjection_desc n v hv, ?_⟩
  intro d hd
  exact unmarkedParameter_hom_ext n (hd.trans (unmarkedParameterProjection_desc n v hv).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
