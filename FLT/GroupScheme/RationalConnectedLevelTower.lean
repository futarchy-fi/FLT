/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentMaps
public import FLT.GroupScheme.PDivisibleSystem

/-! # Connected levels and coherent transitions of an original rational-place system

The levels and both transitions are constructed from the actual system.
Faithful flatness, kernel exactness and a common connected height are still
needed before these data can be bundled as a p-divisible system.
-/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem
  ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual connected component at each original level. -/
abbrev rationalConnectedLevel (n : ℕ) : FF O K := (X.level n).rationalIdentityComponent

/-- The original inclusions restrict to the connected levels. -/
def rationalConnectedInclusion {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.rationalConnectedLevel m) (X.rationalConnectedLevel n) :=
  (X.inclusion h).rationalIdentityMap

/-- The original reductions restrict to the connected levels. -/
def rationalConnectedReduction {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.rationalConnectedLevel n) (X.rationalConnectedLevel m) :=
  (X.reduction h).rationalIdentityMap

/-- Every new level embeds into the original specified level. -/
abbrev rationalConnectedEmbedding (n : ℕ) : ModelHom (X.rationalConnectedLevel n) (X.level n) :=
  (X.level n).rationalIdentityComponentInclusion

/-- The connected inclusion retains the original inclusion square. -/
theorem rationalConnectedInclusion_naturality {m n : ℕ} (h : m ≤ n) :
    (X.rationalConnectedInclusion h).comp (X.rationalConnectedEmbedding n) =
      (X.rationalConnectedEmbedding m).comp (X.inclusion h) :=
  (X.inclusion h).rationalIdentityMap_naturality

/-- The connected reduction retains the original reduction square. -/
theorem rationalConnectedReduction_naturality {m n : ℕ} (h : m ≤ n) :
    (X.rationalConnectedReduction h).comp (X.rationalConnectedEmbedding m) =
      (X.rationalConnectedEmbedding n).comp (X.reduction h) :=
  (X.reduction h).rationalIdentityMap_naturality

/-- Connected inclusions preserve identity levels. -/
theorem rationalConnectedInclusion_refl (n : ℕ) :
    X.rationalConnectedInclusion (le_refl n) = BialgHom.id O _ := by
  rw [rationalConnectedInclusion, X.inclusion_refl, ModelHom.rationalIdentityMap_id]

/-- Connected reductions preserve identity levels. -/
theorem rationalConnectedReduction_refl (n : ℕ) :
    X.rationalConnectedReduction (le_refl n) = BialgHom.id O _ := by
  rw [rationalConnectedReduction, X.reduction_refl, ModelHom.rationalIdentityMap_id]

/-- Connected inclusions obey all original coherence relations. -/
theorem rationalConnectedInclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.rationalConnectedInclusion h).comp (X.rationalConnectedInclusion k) =
      X.rationalConnectedInclusion (h.trans k) := by
  rw [rationalConnectedInclusion, rationalConnectedInclusion, rationalConnectedInclusion,
    ← ModelHom.rationalIdentityMap_comp, X.inclusion_comp]

/-- Connected reductions obey all original coherence relations. -/
theorem rationalConnectedReduction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.rationalConnectedReduction k).comp (X.rationalConnectedReduction h) =
      X.rationalConnectedReduction (h.trans k) := by
  rw [rationalConnectedReduction, rationalConnectedReduction, rationalConnectedReduction,
    ← ModelHom.rationalIdentityMap_comp, X.reduction_comp]

/-- Closedness of the original inclusions descends to the actual connected quotients. -/
theorem rationalConnectedInclusion_closed {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (X.rationalConnectedInclusion h) := by
  intro a
  obtain ⟨b, rfl⟩ := (X.level m).rationalIdentityComponentInclusion_surjective a
  obtain ⟨c, rfl⟩ := X.closed h b
  exact ⟨X.rationalConnectedEmbedding n c,
    DFunLike.congr_fun (X.rationalConnectedInclusion_naturality h) c⟩

/-- The connected geometric points retain the original p-power annihilator. -/
theorem rationalConnectedLevel_killed (n : ℕ) (x : (X.rationalConnectedLevel n).Points) :
    p ^ n • x = 0 := by
  apply (X.level n).rationalIdentityComponentInclusion_genericHom_injective
  rw [map_nsmul, map_zero]
  exact X.killed n _

/-- The lower connected multiplication factors through the original restricted transitions. -/
theorem rationalConnectedInclusion_reduction {m n : ℕ} (h : m ≤ n) :
    (X.rationalConnectedInclusion h).comp (X.rationalConnectedReduction h) =
      (X.rationalConnectedLevel m).multiply (p ^ (n - m)) := by
  rw [rationalConnectedInclusion, rationalConnectedReduction,
    ← ModelHom.rationalIdentityMap_comp, X.inclusion_reduction,
    ModelHom.rationalIdentityMap_multiply]

/-- The higher connected multiplication factors through the original restricted transitions. -/
theorem rationalConnectedReduction_inclusion {m n : ℕ} (h : m ≤ n) :
    (X.rationalConnectedReduction h).comp (X.rationalConnectedInclusion h) =
      (X.rationalConnectedLevel n).multiply (p ^ (n - m)) := by
  rw [rationalConnectedInclusion, rationalConnectedReduction,
    ← ModelHom.rationalIdentityMap_comp, X.reduction_inclusion,
    ModelHom.rationalIdentityMap_multiply]

end ThreeAdicPlan.PDivisibleSystem
