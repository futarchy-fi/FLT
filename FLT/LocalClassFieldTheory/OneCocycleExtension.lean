/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientSequence

/-!
# The extension associated to a one-cocycle

For a one-cocycle `b` with values in `Q`, the action on `Q × k` is
`g(q,t) = (gq + t • b(g), t)`. This constructs the short exact sequence
whose boundary sends `1` to the class of `b`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (Q : Rep k G) (b : cocycles₁ Q)

/-- The twisted action defined by a one-cocycle. -/
def oneCocycleExtension : Rep k G := Rep.of ({
  toFun g := {
    toFun x := (Q.ρ g x.1 + x.2 • b g, x.2)
    map_add' x y := by simp [add_smul]; abel
    map_smul' r x := by simp [smul_add, smul_smul] }
  map_one' := by ext x <;> simp
  map_mul' g h := by
    ext x <;> simp [(mem_cocycles₁_iff b).mp b.property, smul_add] } : Representation k G (Q × k))

/-- Inclusion into the extension. -/
def oneCocycleInclusion : Q ⟶ oneCocycleExtension Q b := Rep.ofHom
  ⟨LinearMap.inl k Q k, fun g => by ext x <;> simp⟩

/-- Projection to the trivial rank-one representation. -/
def oneCocycleProjection : oneCocycleExtension Q b ⟶ Rep.trivial k G k := Rep.ofHom
  ⟨LinearMap.snd k Q k, fun _ => rfl⟩

/-- The actual extension short complex attached to the cocycle. -/
def oneCocycleSequence : ShortComplex (Rep k G) :=
  ShortComplex.mk (oneCocycleInclusion Q b) (oneCocycleProjection Q b) (by ext; rfl)

/-- Twisting the action does not alter exactness of the underlying split modules. -/
theorem oneCocycleSequence_shortExact : (oneCocycleSequence Q b).ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr (fun _ _ h => congrArg Prod.fst h)
  epi_g := (Rep.epi_iff_surjective _).mpr (fun r => ⟨(0, r), rfl⟩)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    rintro ⟨q, r⟩ hr
    exact ⟨q, Prod.ext rfl hr.symm⟩

/-- The boundary of the canonical lift of `1` is precisely the given cocycle. -/
theorem oneCocycle_lift_d :
    (oneCocycleInclusion Q b).hom ∘ b = d₀₁ (oneCocycleExtension Q b) (0, 1) := by
  funext g
  change (b g, 0) = (Q.ρ g 0 + (1 : k) • b g, (1 : k)) - (0, 1)
  simp

/-- The ordinary degree-zero boundary recovers the one-cocycle with positive sign. -/
theorem oneCocycle_connecting_one :
    groupCohomology.δ (oneCocycleSequence_shortExact Q b) 0 1 rfl
      ((H0Iso (Rep.trivial k G k)).inv ⟨(1 : k), fun _ => rfl⟩) = H1π Q b := by
  exact δ₀_apply (oneCocycleSequence_shortExact Q b) ⟨(1 : k), fun _ => rfl⟩ (0, 1) rfl b
    (oneCocycle_lift_d Q b)

end LocalClassFieldTheory
