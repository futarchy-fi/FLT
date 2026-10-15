/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIdeal

/-!
# Infinitesimal neighborhoods over an affine scheme

Powers of an ideal sheaf commute with arbitrary scheme pullback from an affine
target. The resulting closed neighborhoods retain the actual powered ideal,
including its nilpotents, rather than just its closed support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.AffineIdealPower
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)

/-- Powers commute with pullback, even when the test scheme is not affine. -/
theorem comap_pow (f : Y ⟶ X) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap (I ^ n) f ⟨⊤, isAffineOpen_top X⟩ U
    (by simp), Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_comap I f ⟨⊤, isAffineOpen_top X⟩ U (by simp),
    Ideal.map_pow]

/-- Equality of whole pulled-back ideals retains all infinitesimal orders. -/
theorem comap_pow_eq (a b : Y ⟶ X) (h : I.comap a = I.comap b) (n : ℕ) :
    (I ^ n).comap a = (I ^ n).comap b := by
  rw [comap_pow, comap_pow, h]

/-- The exact global equations of a neighborhood are the powers of the original ideal. -/
theorem power_top (n : ℕ) :
    (I ^ n).ideal ⟨⊤, isAffineOpen_top X⟩ =
      I.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n := rfl

omit [IsAffine X]
/-- Positive infinitesimal neighborhoods have the same closed support. -/
theorem power_support (n : ℕ) : (I ^ (n + 1)).support = I.support :=
  Scheme.IdealSheafData.support_pow_succ I n

/-- Higher orders contain lower orders as actual closed subschemes. -/
theorem power_le {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m := by
  intro U
  exact Ideal.pow_le_pow_right h

/-- The canonical inclusion between infinitesimal neighborhoods. -/
def transition {m n : ℕ} (h : m ≤ n) : (I ^ m).subscheme ⟶ (I ^ n).subscheme :=
  Scheme.IdealSheafData.inclusion (power_le I h)

/-- Transitions preserve the entire source scheme map. -/
@[reassoc]
theorem transition_ι {m n : ℕ} (h : m ≤ n) :
    transition I h ≫ (I ^ n).subschemeι = (I ^ m).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- Transition maps satisfy their scheme cocycle law. -/
@[reassoc]
theorem transition_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    transition I h₁ ≫ transition I h₂ = transition I (h₁.trans h₂) := by
  apply (cancel_mono (I ^ n).subschemeι).mp
  rw [Category.assoc, transition_ι, transition_ι, transition_ι]

/-- A transition at the same order is the identity. -/
theorem transition_refl (n : ℕ) : transition I (le_refl n) = 𝟙 _ := by
  apply (cancel_mono (I ^ n).subschemeι).mp
  rw [transition_ι, Category.id_comp]

end FLT.Mazur.AffineIdealPower
