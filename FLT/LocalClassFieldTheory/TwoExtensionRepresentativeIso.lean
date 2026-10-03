/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateTwoClassOperation

/-!
# Isomorphisms between the actual extensions of equal two-classes

The boundary translation has an explicit inverse. Consequently changing the
two-cocycle representative preserves vanishing of the twisted module itself,
in addition to the previously proved equality of its cup operations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G]

/-- Translation by a coboundary is an isomorphism of the concrete twisted modules. -/
def oneCocycleExtensionChangeIso (Q : Rep.{0} k G) (b b' : cocycles₁ Q) (q : Q)
    (h : ∀ g, b g + q = Q.ρ g q + b' g) :
    oneCocycleExtension Q b ≅ oneCocycleExtension Q b' :=
  Rep.mkIso (.mk {
    toFun x := (x.1 + x.2 • q, x.2)
    invFun x := (x.1 - x.2 • q, x.2)
    left_inv x := by ext <;> simp
    right_inv x := by ext <;> simp
    map_add' x y := by simp [add_smul]; abel
    map_smul' r x := by simp [smul_add, smul_smul] } (fun g => by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · change Q.ρ g x.1 + x.2 • b g + x.2 • q =
          Q.ρ g (x.1 + x.2 • q) + x.2 • b' g
        rw [map_add, map_smul, add_assoc, ← smul_add, h, smul_add]
        abel
      · rfl))

/-- Equal two-classes give isomorphic twisted coefficient modules, with no chosen iso premise. -/
def twoExtensionRepresentativeIso (M : Rep.{0} k G) (c c' : cocycles₂ M)
    (h : H2π M c = H2π M c') :
    oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c) ≅
      oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c') := by
  let f := Classical.choose ((H2π_eq_iff c c').mp h)
  have hf := Classical.choose_spec ((H2π_eq_iff c c').mp h)
  exact (oneCocycleExtensionChangeIso (shiftedCoefficients M)
    (shiftedTwoCocycle M c') (shiftedTwoCocycle M c) ((shiftedProjection M).hom f)
    (shiftedTwoCocycle_change M c c' f hf)).symm

/-- Vanishing of the actual twisted module is independent of the two-cocycle representative. -/
theorem twoExtensionRepresentative_isZero_iff [Fintype G]
    (M : Rep.{0} k G) (c c' : cocycles₂ M) (h : H2π M c = H2π M c') (n : ℤ) :
    Limits.IsZero (tateCohomology
      (oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c)) n) ↔
    Limits.IsZero (tateCohomology
      (oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c')) n) := by
  let e := (tateCohomologyFunctor n).mapIso (twoExtensionRepresentativeIso M c c' h)
  exact ⟨fun hx => hx.of_iso e.symm, fun hx => hx.of_iso e⟩

end LocalClassFieldTheory
