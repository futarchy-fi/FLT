/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleLevelTower
public import FLT.GroupScheme.RationalConnectedEtaleExtension
public import FLT.GroupScheme.RationalConnectedTateInclusion

/-! # The inverse limit of the original finite étale quotient levels -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Coherent points of the actual quotient tower, before its p-divisible-system packaging. -/
def rationalEtaleTateSequences : AddSubgroup (∀ n, (X.rationalEtaleLevel n).Points) where
  carrier := {x | ∀ {m n} (h : m ≤ n), genericHom (X.rationalEtaleReduction h) (x n) = x m}
  zero_mem' := by intro m n h; exact map_zero _
  add_mem' := by
    intro x y hx hy m n h
    change genericHom (X.rationalEtaleReduction h) (x n + y n) = x m + y m
    rw [map_add, hx h, hy h]
  neg_mem' := by
    intro x hx m n h
    change genericHom (X.rationalEtaleReduction h) (-x n) = -x m
    rw [map_neg, hx h]

/-- The projection on the actual inverse limits is induced by the original level projections. -/
def rationalEtaleTateProjection : X.tateSequences →+ X.rationalEtaleTateSequences where
  toFun x := ⟨fun n ↦ genericHom (X.rationalEtaleProjection n) (X.tateEval n x), by
    intro m n h
    have he := congrArg (fun f ↦ genericHom f (X.tateEval n x))
      (X.rationalEtaleReduction_naturality h)
    simpa only [genericHom_comp, X.tateEval_reduction] using he⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _

/-- The inverse-limit projection has exactly the original connected Tate module as kernel. -/
theorem rationalEtaleTateProjection_exact (x : X.tateSequences) :
    X.rationalEtaleTateProjection x = 0 ↔
      ∃ a, X.rationalConnectedTateInclusion a = x := by
  constructor
  · intro hx
    have hn (n : ℕ) : ∃ a, genericHom (X.rationalConnectedEmbedding n) a = X.tateEval n x := by
      apply ((X.level n).rationalComponentProjection_points_exact _).mp
      exact congrArg (fun z : X.rationalEtaleTateSequences ↦ z.val n) hx
    choose a ha using hn
    have hc : a ∈ X.rationalConnectedSystem.tateSequences := by
      intro m n h
      apply (X.level m).rationalIdentityComponentInclusion_genericHom_injective
      have he := congrArg (fun f ↦ genericHom f (a n)) (X.rationalConnectedReduction_naturality h)
      change genericHom (X.rationalConnectedEmbedding m)
        (genericHom (X.rationalConnectedReduction h) (a n)) =
        genericHom (X.rationalConnectedEmbedding m) (a m)
      simpa only [genericHom_comp, ha, X.tateEval_reduction] using he
    refine ⟨⟨a, hc⟩, X.tate_ext (fun n ↦ ?_)⟩
    exact ha n
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext n
    exact ((X.level n).rationalComponentProjection_points_exact _).mpr
      ⟨X.rationalConnectedSystem.tateEval n a, rfl⟩
end ThreeAdicPlan.PDivisibleSystem
