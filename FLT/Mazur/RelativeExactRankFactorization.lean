/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafSupportPower
public import FLT.Mazur.RelativeRankPullbackThickenings

/-!
# Finite-order factorization of exact-rank coefficient schemes

On a Noetherian original base, every compact exact-rank coefficient scheme
factors uniquely through some actual rank thickening. This retains its entire
structure sheaf, including nilpotents. The same assertion holds over arbitrary
coefficient schemes by the original rank-stage pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] (n : ℕ)
  {Y : Scheme.{0}} [CompactSpace Y] (f : Y ⟶ S)

/-- A compact exact-rank test has an actual finite-order lift over the original base. -/
theorem exists_rankThickening_factor (hf : Set.range f ⊆ exactRank E n) :
    ∃ (k : ℕ) (g : Y ⟶ rankThickening E n k), g ≫ rankThickeningMap E n k = f := by
  let _ : TopologicalSpace.NoetherianSpace (rankImageOpen E n).toScheme :=
    TopologicalSpace.NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : CompactSpace (rankImageOpen E n).toScheme :=
    TopologicalSpace.NoetherianSpace.compactSpace _
  let _ : AlgebraicGeometry.IsNoetherian (rankImageOpen E n).toScheme :=
    ⟨⟩
  have hr : Set.range f ⊆ Set.range (rankImageOpen E n).ι := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx ↦ (hf hx).1
  let v := IsOpenImmersion.lift (rankImageOpen E n).ι f hr
  have hv : v ≫ (rankImageOpen E n).ι = f := IsOpenImmersion.lift_fac _ _ hr
  have hs : Set.range v ⊆ (rankStratumIdeal E n).support := by
    rintro _ ⟨y, rfl⟩
    change (rankImageOpen E n).ι (v y) ∈ rankAtMost E n
    have he := congrArg (fun a : Y ⟶ S ↦ a y) hv
    exact he ▸ (hf (Set.mem_range_self y)).2
  obtain ⟨k, g, hg⟩ := IdealSheafSupportPower.exists_factor (rankStratumIdeal E n) v hs
  refine ⟨k, g, ?_⟩
  change g ≫ (rankStratumIdeal E n ^ (k + 1)).subschemeι ≫ (rankImageOpen E n).ι = f
  rw [← Category.assoc, hg, hv]

omit [AlgebraicGeometry.IsNoetherian S] [CompactSpace Y] in
/-- A rank-thickening factor is unique at each order. -/
theorem rankThickening_factor_unique (k : ℕ) (g₁ g₂ : Y ⟶ rankThickening E n k)
    (h₁ : g₁ ≫ rankThickeningMap E n k = f)
    (h₂ : g₂ ≫ rankThickeningMap E n k = f) : g₁ = g₂ := by
  have : Mono (rankThickeningMap E n k) := by unfold rankThickeningMap; infer_instance
  exact (cancel_mono (rankThickeningMap E n k)).mp (h₁.trans h₂.symm)

/-- Exact rank detects finite-order factorization, without reducing coefficients. -/
theorem exactRank_iff_rankThickening_factor :
    Set.range f ⊆ exactRank E n ↔
      ∃ (k : ℕ) (g : Y ⟶ rankThickening E n k), g ≫ rankThickeningMap E n k = f := by
  refine ⟨exists_rankThickening_factor E n f, ?_⟩
  rintro ⟨k, g, rfl⟩ _ ⟨y, rfl⟩
  exact (rankThickeningMap_range E n k).le (Set.mem_range_self (g y))

variable {B : Scheme.{0}} (b : B ⟶ S) (v : Y ⟶ B)

/-- The coefficient map factors through a finite original rank stage over that coefficient. -/
theorem exists_rankPullback_factor (hv : Set.range (v ≫ b) ⊆ exactRank E n) :
    ∃ (k : ℕ) (g : Y ⟶ rankPullbackThickening E b n k),
      g ≫ rankPullbackMap E b n k = v := by
  obtain ⟨k, g, hg⟩ := exists_rankThickening_factor E n (v ≫ b) hv
  exact ⟨k, pullback.lift g v hg, pullback.lift_snd _ _ _⟩

end FLT.Mazur.RelativeOrderedTuples
