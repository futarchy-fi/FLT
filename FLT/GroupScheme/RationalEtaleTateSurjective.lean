/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleTateSequences
public import FLT.GroupScheme.FiniteInverseSequence

/-! # Surjectivity on the original inverse limits by finite compatible lifting -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Every coherent quotient point lifts to an original coherent point. -/
theorem rationalEtaleTateProjection_surjective :
    Function.Surjective X.rationalEtaleTateProjection := by
  intro y
  let F (n : ℕ) := {x : (X.level n).Points //
    genericHom (X.rationalEtaleProjection n) x = y.val n}
  let (n : ℕ) : Nonempty (F n) := by
    obtain ⟨x, hx⟩ := (X.level n).rationalComponentProjection_points_surjective (y.val n)
    exact ⟨⟨x, hx⟩⟩
  let r {m n : ℕ} (h : m ≤ n) (x : F n) : F m :=
    ⟨genericHom (X.reduction h) x.val, by
      have he := congrArg (fun f ↦ genericHom f x.val) (X.rationalEtaleReduction_naturality h)
      change genericHom (X.rationalEtaleProjection m) (genericHom (X.reduction h) x.val) = y.val m
      simpa only [genericHom_comp, x.property, y.property h] using he.symm⟩
  obtain ⟨a, ha⟩ := exists_finite_inverse_sequence F r (fun n x ↦ by
    apply Subtype.ext
    change genericHom (X.reduction (le_refl n)) x.val = x.val
    rw [X.reduction_refl, genericHom_id]) (fun h k x ↦ by
    apply Subtype.ext
    change genericHom (X.reduction h) (genericHom (X.reduction k) x.val) = _
    rw [← genericHom_comp, X.reduction_comp])
  refine ⟨⟨fun n ↦ (a n).val, fun h ↦ congrArg Subtype.val (ha h)⟩, ?_⟩
  apply Subtype.ext
  funext n
  exact (a n).property
end ThreeAdicPlan.PDivisibleSystem
