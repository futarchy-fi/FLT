/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteTateNormTower
public import FLT.LocalClassFieldTheory.TwoCocycleInflationSum
public import FLT.LocalClassFieldTheory.NegativeCupArithmetic

/-!
# Inflation and the negative cup in a finite field tower

The comparison is proved on cocycle sums. Inflation contributes the actual
relative degree; this theorem does not cancel it in a norm quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (K E L : Type) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K E] [IsGalois K L] [FiniteDimensional K E] [FiniteDimensional K L]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "ML" => Rep.ofAlgebraAutOnUnits K L
local notation "f" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

/-- The coefficient inclusion for the finite-field tower, with the pulled-back action. -/
def finiteTowerCoefficients : Rep.res f ME ⟶ ML :=
  Rep.ofHom ⟨(Units.map (algebraMap E L).toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Units.ext
      exact g.restrictNormal_commutes E (Additive.toMul u : Eˣ)⟩

/-- Restriction of automorphisms has kernel of the relative field degree. -/
theorem finiteTowerRestriction_card_ker : Nat.card (f).ker = Module.finrank E L := by
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  have hc := Nat.card_congr (homFiberEquiv f (AlgEquiv.restrictNormalHom_surjective L))
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at hc
  have hd := Module.finrank_mul_finrank K E L
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos (hc.trans hd.symm)

/-- Transporting an included invariant back down the tower recovers the same unit. -/
theorem finiteTowerInvariant_inflation (x : (ME).ρ.invariants) :
    finiteTowerInvariantEquiv K E L
      (inflationInvariant ME ML f (finiteTowerCoefficients K E L) x) = x := by
  obtain ⟨u, rfl⟩ := finiteUnitInvariantInclusion_surjective K E x
  have he : inflationInvariant ME ML f (finiteTowerCoefficients K E L)
      (finiteUnitInvariantInclusion K E u) = finiteUnitInvariantInclusion K L u := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply K E L (Additive.toMul u : Kˣ)).symm
  rw [he, finiteTowerInvariantEquiv_unit]

/-- The norm-tower projection on any invariant representative. -/
theorem finiteTateNormTower_class (x : (ML).ρ.invariants) :
    finiteTateNormTower K E L (tateInvariantClass ML x) =
      tateInvariantClass ME (finiteTowerInvariantEquiv K E L x) := by
  obtain ⟨u, rfl⟩ := finiteUnitInvariantInclusion_surjective K L x
  rw [finiteTateNormTower_unit, finiteTowerInvariantEquiv_unit]

/-- The negative cup of an inflated cocycle acquires the relative field degree. -/
theorem finiteTateNormTower_inflated_cup (c : cocycles₂ ME)
    (x : tateCohomology (Rep.trivial ℤ Gal(L/K) ℤ) (-2)) :
    finiteTateNormTower K E L
      (tateTwoExtensionMap ML (mapCocycles₂ f (finiteTowerCoefficients K E L) c) (-2) x) =
      Module.finrank E L • tateTwoExtensionMap ME c (-2) (tateScalarMap f x) := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective Gal(L/K) x
  rw [tateScalarMap_generator, tateTwoExtensionMap_generator,
    tateTwoExtensionMap_generator, finiteTateNormTower_class,
    twoCocycleSumInvariant_inflation ME ML f (finiteTowerCoefficients K E L)
      (AlgEquiv.restrictNormalHom_surjective L), map_nsmul,
    finiteTowerInvariant_inflation, finiteTowerRestriction_card_ker, map_inv]
  exact map_nsmul (tateInvariantClass ME).hom _ _

/-- The degree-weighted comparison depends only on the ordinary two-class. -/
theorem finiteTateNormTower_inflated_class (a : groupCohomology ME 2)
    (x : tateCohomology (Rep.trivial ℤ Gal(L/K) ℤ) (-2)) :
    finiteTateNormTower K E L
      (tateTwoClassMap ML (groupCohomology.map f (finiteTowerCoefficients K E L) 2 a) (-2) x) =
      Module.finrank E L • tateTwoClassMap ME a (-2) (tateScalarMap f x) := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π ME)).mp inferInstance a
  have hr := congrArg (fun q => q.hom c) (H2π_comp_map f (finiteTowerCoefficients K E L))
  change groupCohomology.map f (finiteTowerCoefficients K E L) 2 (H2π ME c) =
    H2π ML (mapCocycles₂ f (finiteTowerCoefficients K E L) c) at hr
  rw [hr, tateTwoClassMap_class, tateTwoClassMap_class]
  exact finiteTateNormTower_inflated_cup K E L c x

end LocalClassFieldTheory
