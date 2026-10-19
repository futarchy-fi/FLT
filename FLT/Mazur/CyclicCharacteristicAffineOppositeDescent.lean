/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOppositeCover

/-!
# Descent of full affine residual invariants to the opposite domain

The restricted transition family compares full original subgroup parameters.
Its effective epimorphism property reconstructs any residual-invariant scheme
map on the exact opposite-chart domain, with the original cover equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) (j : (invariantAffineCover n (!b)).I₀)
local notation "i" => (Sigma.mk (!b) j : InvariantAffineIndex n)

/-- The pulled transition source is the original opposite-chart parameter. -/
@[reassoc] theorem affineOppositeCover_source (k : (transitionCover n b).I₀) :
    pullback.snd (affineOppositeToTransition n b j) ((transitionCover n b).f k) ≫
      transitionSource n b k =
        (affineOppositeCover n b j).f k ≫ (affineOppositeOpen n b j).ι := by
  rw [transitionSource, ← Category.assoc, ← pullback.condition, Category.assoc,
    affineOppositeToTransition_comp]
  rfl

/-- The restricted cover compares the same full original families in both charts. -/
theorem affineOppositeCover_related (k : (transitionCover n b).I₀) :
    UnmarkedRelated n (!b) b
      (affineOppositeTarget n b j k ≫ invariantAffineInclusion n i)
      ((affineOppositeCover n b j).f k ≫ (affineOppositeOpen n b j).ι) := by
  rw [affineOppositeTarget_inclusion, ← affineOppositeCover_source]
  exact UnmarkedRelated.baseChange n (transition_unmarkedRelated n b k) _

/-- Coincident source tests have fully compatible affine target parameters. -/
theorem affineOppositeTarget_related {T : Scheme}
    (k l : (affineOppositeCover n b j).I₀)
    (g : T ⟶ (affineOppositeCover n b j).X k)
    (h : T ⟶ (affineOppositeCover n b j).X l)
    (he : g ≫ (affineOppositeCover n b j).f k =
      h ≫ (affineOppositeCover n b j).f l) :
    UnmarkedRelated n (!b) (!b)
      ((g ≫ affineOppositeTarget n b j k) ≫ invariantAffineInclusion n i)
      ((h ≫ affineOppositeTarget n b j l) ≫ invariantAffineInclusion n i) := by
  have hk := UnmarkedRelated.baseChange n (affineOppositeCover_related n b j k) g
  have hl := UnmarkedRelated.baseChange n (affineOppositeCover_related n b j l) h
  simp only [← Category.assoc] at hk hl
  rw [he] at hk
  exact UnmarkedRelated.trans n hk (UnmarkedRelated.symm n hl)

variable {Y : Scheme} (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y)
  (hf : affineResidualSource n ⟨!b, j⟩ ≫ f = affineResidualTarget n ⟨!b, j⟩ ≫ f)

/-- Full residual invariance gives compatible values on the restricted fppf family. -/
theorem affineOpposite_compatible
    (hf : affineResidualSource n i ≫ f = affineResidualTarget n i ≫ f) {T : Scheme}
    (k l : (affineOppositeCover n b j).I₀)
    (g : T ⟶ (affineOppositeCover n b j).X k)
    (h : T ⟶ (affineOppositeCover n b j).X l)
    (he : g ≫ (affineOppositeCover n b j).f k =
      h ≫ (affineOppositeCover n b j).f l) :
    g ≫ affineOppositeTarget n b j k ≫ f = h ≫ affineOppositeTarget n b j l ≫ f := by
  simpa only [Category.assoc] using affineResidual_invariant_on_test n i f hf _ _
    (affineOppositeTarget_related n b j k l g h he)

/-- Reconstruct an actual scheme map on the opposite part of the affine quotient domain. -/
def affineOppositeDescend : (affineOppositeOpen n b j).toScheme ⟶ Y := by
  let _ := SchemeFppfFamily.effectiveEpiFamily (affineOppositeCover n b j)
  exact EffectiveEpiFamily.desc (affineOppositeCover n b j).X
    (affineOppositeCover n b j).f (fun k => affineOppositeTarget n b j k ≫ f)
    (fun {_} k l g h he => affineOpposite_compatible n b j f hf k l g h he)

/-- The descended morphism retains every actual restricted transition pullback. -/
@[reassoc] theorem affineOppositeDescend_fac (k : (affineOppositeCover n b j).I₀) :
    (affineOppositeCover n b j).f k ≫ affineOppositeDescend n b j f hf =
      affineOppositeTarget n b j k ≫ f := by
  let _ := SchemeFppfFamily.effectiveEpiFamily (affineOppositeCover n b j)
  exact EffectiveEpiFamily.fac (affineOppositeCover n b j).X
    (affineOppositeCover n b j).f (fun l => affineOppositeTarget n b j l ≫ f)
    (fun {_} l m g h he => affineOpposite_compatible n b j f hf l m g h he) k

/-- The actual restricted transition family determines reconstruction uniquely. -/
theorem affineOppositeDescend_unique (g : (affineOppositeOpen n b j).toScheme ⟶ Y)
    (hg : ∀ k, (affineOppositeCover n b j).f k ≫ g =
      affineOppositeTarget n b j k ≫ f) : g = affineOppositeDescend n b j f hf := by
  apply SchemeFppfFamily.cover_hom_ext (affineOppositeCover n b j)
  intro k
  rw [hg, affineOppositeDescend_fac]

end FLT.Mazur.CyclicCharacteristicOrbit
