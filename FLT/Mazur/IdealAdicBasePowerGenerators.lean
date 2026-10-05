/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedPullback

/-!
# Base power generators on affine source opens

For an affine base, the canonical comparison images of base power sections
span the actual extended ideal module on every affine source open. The
statement uses the original comparison, and requires no flatness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Restrict the actual power comparison of a global base section to a source open. -/
def powerSection (n : ℕ) (U : X.Opens) (s : Γ(idealModule (J ^ n), ⊤)) :
    Γ(idealModule (J.comap f ^ n), U) :=
  (idealModule (J.comap f ^ n)).presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op
    ((powerMap J f n).app ⊤ s)

/-- The generators have their original scheme-theoretic coordinate values. -/
lemma powerSection_inclusion (n : ℕ) (U : X.Opens)
    (s : Γ(idealModule (J ^ n), ⊤)) :
    (idealModuleι (J.comap f ^ n)).app U (powerSection J f n U s) =
      (f.appLE ⊤ U (by simp)) ((idealModuleι (J ^ n)).app ⊤ s) := by
  unfold powerSection
  have h := PresheafOfModules.naturality_apply (idealModuleι (J.comap f ^ n)).val
    (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op ((powerMap J f n).app ⊤ s)
  exact h.trans (congrArg (X.presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op)
    (powerMap_inclusion J f n ⊤ s))

/-- The images of base power sections span every affine extended power module. -/
lemma powerSection_span [IsAffine Y] (n : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U.1) (Set.range (powerSection J f n U.1)) = ⊤ := by
  let P := Submodule.span Γ(X, U.1) (Set.range (powerSection J f n U.1))
  let i := ((idealModuleι (J.comap f ^ n)).val.app (op U.1)).hom
  have h : (J.comap f ^ n).ideal U ≤ P.map i := by
    have he : (J.comap f ^ n).ideal U =
        ((J ^ n).ideal ⟨⊤, isAffineOpen_top Y⟩).map (f.appLE ⊤ U.1 (by simp)).hom := by
      rw [← idealSheaf_comap_pow, ideal_comap (J ^ n) f ⟨⊤, isAffineOpen_top Y⟩ U (by simp)]
    rw [he]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    let s := (idealModuleAffineEquiv (J ^ n) ⟨⊤, isAffineOpen_top Y⟩).symm ⟨r, hr⟩
    refine ⟨powerSection J f n U.1 s, Submodule.subset_span ⟨s, rfl⟩, ?_⟩
    change (idealModuleι (J.comap f ^ n)).app U.1 (powerSection J f n U.1 s) = _
    rw [powerSection_inclusion]
    have hs : (idealModuleι (J ^ n)).app ⊤ s = r := by
      rw [← idealModuleAffineEquiv_val (J ^ n) ⟨⊤, isAffineOpen_top Y⟩]
      exact congrArg Subtype.val
        ((idealModuleAffineEquiv (J ^ n) ⟨⊤, isAffineOpen_top Y⟩).apply_symm_apply ⟨r, hr⟩)
    exact congrArg (f.appLE ⊤ U.1 (by simp)) hs
  apply top_unique
  intro t _
  have ht := h (idealModuleAffineEquiv (J.comap f ^ n) U t).property
  obtain ⟨s, hs, he⟩ := ht
  have hst : s = t := by
    apply (idealModuleAffineEquiv (J.comap f ^ n) U).injective
    apply Subtype.ext
    rw [idealModuleAffineEquiv_val]
    exact he
  exact hst ▸ hs

end FLT.Mazur.IdealAdicGradedPullback
