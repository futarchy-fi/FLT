/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Ordinary connecting maps and group restriction

A morphism of coefficient sequences over a group homomorphism gives a
morphism of the actual cochain short complexes. Their connecting squares
commute, including inflation from a quotient group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (f : G →* H) {S : ShortComplex (Rep.{0} k H)} {T : ShortComplex (Rep.{0} k G)}
  (u : S.map (Rep.resFunctor f) ⟶ T)

/-- Pullback of arguments and the coefficient maps give a morphism of cochain sequences. -/
def groupRestrictionSequenceMap :
    S.map (cochainsFunctor k H) ⟶ T.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f u.τ₁
  τ₂ := cochainsMap f u.τ₂
  τ₃ := cochainsMap f u.τ₃
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext x
    exact congrArg (fun v => v.hom (c (f ∘ x))) u.comm₁₂
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext x
    exact congrArg (fun v => v.hom (c (f ∘ x))) u.comm₂₃

/-- Ordinary connecting maps commute with group restriction and compatible coefficients. -/
theorem groupConnecting_restriction (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl ≫ groupCohomology.map f u.τ₁ (n + 1) =
      groupCohomology.map f u.τ₃ n ≫ groupCohomology.δ hT n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality (groupRestrictionSequenceMap f u)
    (map_cochainsFunctor_shortExact hS) (map_cochainsFunctor_shortExact hT) n (n + 1) rfl

/-- On the scalar H⁰ unit, restriction with a scalar coefficient map multiplies by that scalar. -/
theorem groupScalarUnit_map (r : k) :
    groupCohomology.map f (r • 𝟙 (Rep.trivial k G k)) 0
      ((H0Iso (Rep.trivial k H k)).inv ⟨(1 : k), fun _ => rfl⟩) =
        r • (H0Iso (Rep.trivial k G k)).inv ⟨(1 : k), fun _ => rfl⟩ := by
  apply (ModuleCat.mono_iff_injective (H0Iso (Rep.trivial k G k)).hom).mp inferInstance
  apply Subtype.ext
  have h := map_H0Iso_hom_f_apply f (r • 𝟙 (Rep.trivial k G k))
    ((H0Iso (Rep.trivial k H k)).inv ⟨(1 : k), fun _ => rfl⟩)
  rw [Iso.inv_hom_id_apply] at h
  simp only [map_smul, Iso.inv_hom_id_apply]
  exact h

end LocalClassFieldTheory
