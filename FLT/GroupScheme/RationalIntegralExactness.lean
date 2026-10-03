/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIntegralTransition
public import FLT.GroupScheme.IntegralClosedImmersion
public import FLT.GroupScheme.IntegralQuotientIdentification

/-!
# Rigidity and closed inclusions over the rational prime completion

Unique extension of the inverse generic map proves integral rigidity.
The flat closure comparison then identifies every prescribed generic inclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open NumberField
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Extending the inverse proves rigidity when the target is killed by a p-power. -/
theorem ModelHom.surjective_of_rational_target {X Y : FF O K}
    (hp : 2 < p) (hY : KilledByPowerOf p Y) (f : ModelHom X Y)
    (hf : Function.Bijective (genericHom f)) : Function.Surjective f := by
  let g := (genericHom f).inverse hf
  let i := g.rationalExtension p hp hY
  have hi : f.comp i = BialgHom.id O X.CoordinateRing := by
    apply genericHom_injective
    ext x
    simp only [genericHom_comp, i, GenericGaloisHom.genericHom_rationalExtension,
      g, GenericGaloisHom.inverse_apply, genericHom_id]
  intro x
  exact ⟨i x, DFunLike.congr_fun hi x⟩

/-- Generic isomorphisms from p-power levels are surjective on integral coordinates. -/
theorem ModelHom.surjective_of_rational_power {X Y : FF O K}
    (hp : 2 < p) (hX : KilledByPowerOf p X) (f : ModelHom X Y)
    (hf : Function.Bijective (genericHom f)) : Function.Surjective f := by
  apply f.surjective_of_rational_target p hp _ hf
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [← map_nsmul, hn, map_zero]

/-- Every generically injective map from a p-power model is an integral closed immersion. -/
theorem ModelHom.closed_of_rational_power {X Y : FF O K}
    (hp : 2 < p) (hX : KilledByPowerOf p X) (f : ModelHom X Y)
    (hf : Function.Injective (genericHom f)) : Function.Surjective f := by
  have hc : Function.Bijective (genericHom (f.closureComparison hf)) := by
    constructor
    · intro x y h
      simpa only [ModelHom.closureComparisonPoints] using h
    · exact fun x ↦ ⟨x, f.closureComparisonPoints hf x⟩
  have hs := (f.closureComparison hf).surjective_of_rational_power p hp hX hc
  intro x
  obtain ⟨y, rfl⟩ := hs x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, DFunLike.congr_fun (f.closureComparisonInclusion hf) z⟩

/-- A prescribed quotient's comparison with its contracted quotient is generically identity. -/
theorem ModelHom.quotientComparisonPoints {X Y : FF O K} (f : ModelHom X Y)
    (hf : Function.Surjective (genericHom f)) (y : Y.Points) :
    genericHom (f.quotientComparison hf) y = y := by
  obtain ⟨x, rfl⟩ := hf y
  have h := congrArg (fun g : ModelHom X Y ↦ genericHom g x)
    (f.quotientComparisonComp hf)
  simpa only [genericHom_comp, GenericGaloisHom.genericHom_toFlatQuotient] using h

/-- The prescribed p-power quotient is isomorphic to the contracted quotient model. -/
theorem ModelHom.quotientComparison_bijective {X Y : FF O K}
    (hp : 2 < p) (hY : KilledByPowerOf p Y) (f : ModelHom X Y)
    (hf : Function.Surjective (genericHom f)) :
    Function.Bijective (f.quotientComparison hf) := by
  have hc : Function.Bijective (genericHom (f.quotientComparison hf)) := by
    constructor
    · intro x y h
      simpa only [ModelHom.quotientComparisonPoints] using h
    · exact fun y ↦ ⟨y, f.quotientComparisonPoints p hf y⟩
  exact ⟨ModelHom.injective_of_baseChange_injective _
      ((f.quotientComparison hf).baseChange_bijective hc).1,
    (f.quotientComparison hf).surjective_of_rational_target p hp hY hc⟩

end ThreeAdicPlan
