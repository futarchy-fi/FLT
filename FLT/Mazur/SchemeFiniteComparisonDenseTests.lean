/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteEndpointComparison

/-!
# Dense coverage of full finite comparison tests

Closedness propagates dense actual image coverage to the whole coefficient
scheme. Reduced coefficients give a unique full lift. On nonreduced compact
coefficients only nilpotence follows; no infinitesimal equations are discarded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D T B : Scheme.{0}} (c : D ⟶ T) (b : B ⟶ T)
  [IsFinite (pullback.snd c b)]

/-- Dense actual comparison coverage covers the entire full finite coefficient test. -/
theorem comparison_surjective_of_dense (h : Dense (b ⁻¹' Set.range c)) :
    Surjective (pullback.snd c b) := by
  constructor
  intro u
  have hu := h u
  rw [← Scheme.Pullback.range_snd,
    (pullback.snd c b).isClosedMap.isClosed_range.closure_eq] at hu
  exact hu

/-- A reduced coefficient scheme admits an actual isomorphism, without irreducibility. -/
theorem comparison_isIso_of_dense [Mono c] [IsReduced B]
    (h : Dense (b ⁻¹' Set.range c)) : IsIso (pullback.snd c b) := by
  let _ := (IsClosedImmersion.iff_isFinite_and_mono (pullback.snd c b)).mpr
    ⟨inferInstance, inferInstance⟩
  let _ := comparison_surjective_of_dense c b h
  exact isIso_of_isClosedImmersion_of_surjective (pullback.snd c b)

/-- The isomorphism constructs a unique full arrow on a possibly reducible reduced test. -/
theorem comparison_unique_lift_of_dense [Mono c] [IsReduced B]
    (h : Dense (b ⁻¹' Set.range c)) : ∃! d : B ⟶ D, d ≫ c = b := by
  let _ := comparison_isIso_of_dense c b h
  refine ⟨inv (pullback.snd c b) ≫ pullback.fst c b, ?_, ?_⟩
  · change (inv (pullback.snd c b) ≫ pullback.fst c b) ≫ c = b
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro d hd
    apply (cancel_mono c).mp
    rw [hd, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- On compact nonreduced tests, every original comparison equation becomes nilpotent. -/
theorem comparison_kernel_isNilpotent_of_dense [CompactSpace B]
    (h : Dense (b ⁻¹' Set.range c)) (r : Γ(T, ⊤)) (hr : c.appTop r = 0) :
    IsNilpotent (b.appTop r) := by
  let _ := comparison_surjective_of_dense c b h
  have hz : (pullback.snd c b).appTop (b.appTop r) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      ← pullback.condition, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
      hr, map_zero]
  apply (Scheme.isNilpotent_iff_basicOpen_eq_bot _).mpr
  apply eq_bot_iff.mpr
  intro u hu
  obtain ⟨v, rfl⟩ := (pullback.snd c b).surjective u
  change v ∈ (pullback.snd c b) ⁻¹ᵁ B.basicOpen (b.appTop r) at hu
  rw [Scheme.preimage_basicOpen_top, hz, Scheme.basicOpen_zero] at hu
  exact hu

end FLT.Mazur.SchemeFiniteEndpointComparison
