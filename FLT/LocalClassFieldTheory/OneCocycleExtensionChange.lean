/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtension

/-!
# Changing an extension cocycle by a boundary

A translation in the first coordinate compares the two concrete extensions.
Naturality of the Tate boundary proves equality in all degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (Q : Rep k G)
  (b b' : cocycles₁ Q) (q : Q) (h : ∀ g, b g + q = Q.ρ g q + b' g)

/-- Translation of the first coordinate compares cohomologous extensions. -/
def oneCocycleExtensionChange : oneCocycleExtension Q b ⟶ oneCocycleExtension Q b' :=
  Rep.ofHom ⟨{
    toFun x := (x.1 + x.2 • q, x.2)
    map_add' x y := by simp [add_smul]; abel
    map_smul' r x := by simp [smul_add, smul_smul] }, fun g => by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · change Q.ρ g x.1 + x.2 • b g + x.2 • q =
          Q.ρ g (x.1 + x.2 • q) + x.2 • b' g
        rw [map_add, map_smul, add_assoc, ← smul_add, h, smul_add]
        abel
      · rfl⟩

/-- A morphism of short exact sequences fixing both ends. -/
def oneCocycleSequenceChange : oneCocycleSequence Q b ⟶ oneCocycleSequence Q b' where
  τ₁ := 𝟙 Q
  τ₂ := oneCocycleExtensionChange Q b b' q h
  τ₃ := 𝟙 _
  comm₁₂ := by
    ext x
    change Q at x
    change (x, (0 : k)) = (x + (0 : k) • q, (0 : k))
    simp
  comm₂₃ := by ext; rfl

variable [Fintype G]

include h in
/-- Cohomologous one-cocycles give the same Tate connecting map in every degree. -/
theorem oneCocycle_tateConnecting_change (n : ℤ) :
    TateCohomology.δ (oneCocycleSequence_shortExact Q b) n =
      TateCohomology.δ (oneCocycleSequence_shortExact Q b') n := by
  have hn := TateCohomology.δ_naturality (oneCocycleSequence_shortExact Q b)
    (oneCocycleSequence_shortExact Q b') (oneCocycleSequenceChange Q b b' q h) n
  have h₁ := (tateCohomologyFunctor (R := k) (G := G) (n + 1)).map_id Q
  have h₃ := (tateCohomologyFunctor (R := k) (G := G) n).map_id (Rep.trivial k G k)
  dsimp only [oneCocycleSequenceChange, oneCocycleSequence] at hn
  rw [h₁, h₃, Category.comp_id, Category.id_comp] at hn
  exact hn

end LocalClassFieldTheory
