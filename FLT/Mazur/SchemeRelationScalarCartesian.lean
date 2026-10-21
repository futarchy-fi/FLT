/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarEtale

/-!
# Scalar extension of an original full kernel pair

An original cartesian relation remains cartesian over every scalar extension
and over its exact image. No flatness, etaleness or new coverage is required
for this preservation theorem; the full original kernel-pair input is explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S)
local notation "g" => Spec.map (CommRingCat.ofHom ρ)
local notation "c" => SchemeScalarImageQuotient.projection (pullback.snd f g)

/-- Full scalar extension preserves the original cartesian relation. -/
theorem scalar_isPullback_of_original (H : IsPullback a b f f) :
    IsPullback (first a f ρ) (second a b f h ρ) (pullback.snd f g) (pullback.snd f g) := by
  have outer := (first_isPullback a f ρ).paste_horiz H.flip
  have outer' : IsPullback (second a b f h ρ ≫ pullback.fst f g)
      (first a f ρ) f (pullback.snd f g ≫ g) := by
    rw [second_original, ← pullback.condition]
    exact outer
  exact (outer'.of_right (scalar_condition a b f h ρ).symm
    (IsPullback.of_hasPullback f g)).flip

/-- Passing to the exact image preserves the whole scalar kernel pair. -/
theorem image_isPullback_of_original (H : IsPullback a b f f) :
    IsPullback (first a f ρ) (second a b f h ρ) c c := by
  have H' := scalar_isPullback_of_original a b f h ρ H
  apply IsPullback.of_isLimit («c» :=
    PullbackCone.mk _ _ (image_condition a b f h ρ))
  apply PullbackCone.isLimitAux'
  intro s
  have hs := (SchemeScalarImageQuotient.projection_eq_iff _ s.fst s.snd).mp s.condition
  refine ⟨H'.lift s.fst s.snd hs, H'.lift_fst _ _ _, H'.lift_snd _ _ _, ?_⟩
  intro m hm₁ hm₂
  exact H'.hom_ext (hm₁.trans (H'.lift_fst _ _ _).symm)
    (hm₂.trans (H'.lift_snd _ _ _).symm)

/-- The canonical full comparison is an isomorphism, with no separate coverage assumption. -/
theorem kernelComparison_isIso_of_original (H : IsPullback a b f f) :
    IsIso (kernelComparison a b f h ρ) := by
  have he : kernelComparison a b f h ρ =
      (image_isPullback_of_original a b f h ρ H).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [kernelComparison_first, IsPullback.isoPullback_hom_fst]
    · rw [kernelComparison_second, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

end FLT.Mazur.SchemeRelationScalarBaseChange
