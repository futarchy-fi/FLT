/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedRestrictionComparison

/-!
# Restricting the concrete twisted extension

Restricting the coinduced primitive gives the primitive of the restricted
two-cocycle. This constructs the comparison of the actual twisted sequences,
and identifies their connecting maps after the proved coefficient comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (M : Rep.{0} k G) (f : H →* G) (c : cocycles₂ M)

local notation "Mc" => Rep.res f M
local notation "cr" => mapCocycles₂ f (𝟙 Mc) c
local notation "Q" => shiftedCoefficients M
local notation "Qr" => shiftedCoefficients Mc

/-- Restriction of the concrete primitive is the primitive of the pulled-back cocycle. -/
theorem twoCocyclePrimitive_restriction (g : H) :
    (coinducedRestriction M f).hom (twoCocyclePrimitive M c (f g)) =
      twoCocyclePrimitive Mc cr g := rfl

/-- The coefficient quotient comparison carries the shifted cocycle to the subgroup shift. -/
theorem shiftedTwoCocycle_restriction (g : H) :
    (shiftedRestriction M f).hom (shiftedTwoCocycle M c (f g)) =
      shiftedTwoCocycle Mc cr g := rfl

/-- Compare the restricted twisted module with the module constructed after restriction. -/
def twoExtensionRestriction :
    Rep.res f (oneCocycleExtension Q (shiftedTwoCocycle M c)) ⟶
      oneCocycleExtension Qr (shiftedTwoCocycle Mc cr) :=
  Rep.ofHom ⟨{
    toFun x := ((shiftedRestriction M f).hom x.1, x.2)
    map_add' x y := by
      change ((shiftedRestriction M f).hom (x.1 + y.1), x.2 + y.2) =
        ((shiftedRestriction M f).hom x.1 + (shiftedRestriction M f).hom y.1, x.2 + y.2)
      rw [map_add]
    map_smul' r x := by
      change ((shiftedRestriction M f).hom (r • x.1), r • x.2) =
        (r • (shiftedRestriction M f).hom x.1, r • x.2)
      rw [map_smul] }, fun g => by
      ext x : 1
      apply Prod.ext
      · change (shiftedRestriction M f).hom
          ((Rep.res f Q).ρ g x.1 + x.2 • shiftedTwoCocycle M c (f g)) = _
        rw [map_add, map_smul, Rep.hom_comm_apply]
        rfl
      · rfl⟩

/-- The actual twisted short exact sequences are related by the quotient comparison. -/
def twoExtensionRestrictionSequence :
    (oneCocycleSequence Q (shiftedTwoCocycle M c)).map (Rep.resFunctor f) ⟶
      oneCocycleSequence Qr (shiftedTwoCocycle Mc cr) where
  τ₁ := shiftedRestriction M f
  τ₂ := twoExtensionRestriction M f c
  τ₃ := 𝟙 _
  comm₁₂ := by ext x; rfl
  comm₂₃ := by ext x; rfl

/-- Restriction preserves the concrete twisted short exact sequence. -/
theorem twoExtensionRestriction_shortExact :
    ((oneCocycleSequence Q (shiftedTwoCocycle M c)).map (Rep.resFunctor f)).ShortExact :=
  (Rep.shortExact_res f).mpr (oneCocycleSequence_shortExact Q (shiftedTwoCocycle M c))

variable [Fintype H]

/-- The first boundary is compatible with the constructed restricted twisted sequence. -/
theorem twoExtensionRestriction_boundary (n : ℤ) :
    TateCohomology.δ (twoExtensionRestriction_shortExact M f c) n ≫
        (tateCohomologyFunctor (n + 1)).map (shiftedRestriction M f) =
      TateCohomology.δ (oneCocycleSequence_shortExact Qr (shiftedTwoCocycle Mc cr)) n := by
  have h := TateCohomology.δ_naturality (twoExtensionRestriction_shortExact M f c)
    (oneCocycleSequence_shortExact Qr (shiftedTwoCocycle Mc cr))
    (twoExtensionRestrictionSequence M f c) n
  have hi := (tateCohomologyFunctor (R := k) (G := H) n).map_id
    (((oneCocycleSequence Q (shiftedTwoCocycle M c)).map (Rep.resFunctor f)).X₃)
  dsimp only [twoExtensionRestrictionSequence] at h
  rw [hi, Category.id_comp] at h
  exact h

end LocalClassFieldTheory
