/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.QuotientBoundaryDescent

/-!
# Injectivity of ordinary quotient inflation

Vanishing of subgroup H¹ corrects an inflated bounding cochain to vanish
on the subgroup. Its normalized boundary then descends to the quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)
  (N : Subgroup G) [N.Normal]
  (h₁ : Limits.IsZero (groupCohomology (Rep.res N.subtype M) 1))

local notation "MQ" => M.quotientToInvariants N
local notation "q" => QuotientGroup.mk' N
local notation "ι" => quotientInflationCoefficients M N

include h₁ in
/-- Every ordinary boundary of an inflated two-cocycle descends. -/
theorem quotientInflation_boundary_reflects (c : cocycles₂ MQ) (b : G → M)
    (hb : ∀ g h, M.ρ g (b h) - b (g * h) + b g = (c (q g, q h)).val) :
    ∃ d : (G ⧸ N) → MQ, d₁₂ MQ d = c := by
  let u : MQ := c (1, 1)
  let cn : (G ⧸ N) × (G ⧸ N) → MQ := fun v => c v - (MQ).ρ v.1 u
  have hc0 (g : G ⧸ N) : cn (g, 1) = 0 := by
    exact sub_eq_zero.mpr (cocycles₂_map_one_snd c g)
  have hc1 (g : G ⧸ N) : cn (1, g) = 0 := by
    change c (1, g) - (MQ).ρ 1 u = 0
    rw [cocycles₂_map_one_fst, map_one, Module.End.one_apply, sub_self]
  let d : G → M := fun g => b g - u.val
  have hd (g h : G) : M.ρ g (d h) - d (g * h) + d g = (cn (q g, q h)).val := by
    change M.ρ g (b h - u.val) - (b (g * h) - u.val) + (b g - u.val) =
      (c (q g, q h)).val - M.ρ g u.val
    rw [map_sub]
    calc
      _ = (M.ρ g (b h) - b (g * h) + b g) - M.ρ g u.val := by abel
      _ = _ := by rw [hb]
  let z : cocycles₁ (Rep.res N.subtype M) := ⟨fun n => d n, by
    apply (mem_cocycles₁_def _).mpr
    intro n m
    have hn : q (n : G) = 1 := (QuotientGroup.eq_one_iff _).mpr n.property
    have hm : q (m : G) = 1 := (QuotientGroup.eq_one_iff _).mpr m.property
    have h := hd n m
    rw [hn, hm, hc0] at h
    exact h⟩
  have hz : H1π (Rep.res N.subtype M) z = 0 :=
    (ModuleCat.subsingleton_of_isZero h₁).elim _ _
  obtain ⟨a, ha⟩ := (H1π_eq_zero_iff z).mp hz
  let e : G → M := fun g => d g - (M.ρ g a - a)
  have heN (n : N) : e n = 0 := by
    exact sub_eq_zero.mpr (congrFun ha n).symm
  have he (g h : G) : M.ρ g (e h) - e (g * h) + e g = (cn (q g, q h)).val := by
    change M.ρ g (d h - (M.ρ h a - a)) - (d (g * h) - (M.ρ (g * h) a - a)) +
      (d g - (M.ρ g a - a)) = _
    simp only [map_sub, map_mul, Module.End.mul_apply]
    calc
      _ = M.ρ g (d h) - d (g * h) + d g := by
        dsimp only [d]
        simp only [map_sub]
        abel
      _ = _ := hd g h
  obtain ⟨v, hv⟩ := quotientBoundary_descends M N cn e he heN hc0 hc1
  refine ⟨fun g => v g + u, ?_⟩
  funext gh
  have hh := congrFun hv gh
  change (MQ).ρ gh.1 (v gh.2) - v (gh.1 * gh.2) + v gh.1 =
    c gh - (MQ).ρ gh.1 u at hh
  change (MQ).ρ gh.1 (v gh.2 + u) - (v (gh.1 * gh.2) + u) + (v gh.1 + u) = c gh
  rw [map_add]
  calc
    _ = ((MQ).ρ gh.1 (v gh.2) - v (gh.1 * gh.2) + v gh.1) + (MQ).ρ gh.1 u := by abel
    _ = _ := by rw [hh, sub_add_cancel]

include h₁ in
/-- Quotient inflation on ordinary H² is injective when subgroup H¹ vanishes. -/
theorem quotientInflationH2_injective :
    Function.Injective (groupCohomology.map q ι 2) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π MQ)).mp inferInstance x
  have hm := congrArg (fun t => t.hom c) (H2π_comp_map q ι)
  change groupCohomology.map q ι 2 (H2π MQ c) = H2π M (mapCocycles₂ q ι c) at hm
  rw [hm, H2π_eq_zero_iff] at hx
  obtain ⟨b, hb⟩ := hx
  apply (H2π_eq_zero_iff c).mpr
  obtain ⟨d, hd⟩ := quotientInflation_boundary_reflects M N h₁ c b
    (fun g h => congrFun hb (g, h))
  exact ⟨d, hd⟩

end LocalClassFieldTheory
