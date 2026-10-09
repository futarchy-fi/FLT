/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# The open charts of a scheme pushout

Both charts of an open gluing are open immersions and jointly cover the
result. These statements apply to enlarged, nonaffine exteriors as well.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeOpenPushout
variable {O E X : Scheme} (e : O ⟶ E) (x : O ⟶ X)
  [IsOpenImmersion e] [IsOpenImmersion x]

instance inl_isOpenImmersion : IsOpenImmersion (pushout.inl e x) := by
  change IsOpenImmersion (colimit.ι (span e x) WalkingSpan.left)
  infer_instance

instance inr_isOpenImmersion : IsOpenImmersion (pushout.inr e x) := by
  change IsOpenImmersion (colimit.ι (span e x) WalkingSpan.right)
  infer_instance

/-- Every point of an open gluing lies in one of its two original charts. -/
theorem charts_cover (z : (pushout e x : Scheme)) :
    (∃ a, pushout.inl e x a = z) ∨ ∃ a, pushout.inr e x a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span e x) z
  cases i with
  | none =>
    left
    refine ⟨e a, ?_⟩
    change (e ≫ pushout.inl e x) a = z
    rw [show e ≫ pushout.inl e x = colimit.ι (span e x) WalkingSpan.zero from
      colimit.w (span e x) WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

end FLT.Mazur.SchemeOpenPushout
