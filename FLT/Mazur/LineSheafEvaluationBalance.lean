/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafBidual

/-!
# Balanced contraction on a line sheaf

A functional on a line may be evaluated on either of two sections before
scaling the other one. The identity is checked on actual trivializing opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

/-- The rank-one contraction identity for any chosen linear coordinate. -/
lemma linearFunctional_balance {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    (e : V ≃ₗ[R] R) (φ : V →ₗ[R] R) (s t : V) : φ s • t = φ t • s := by
  have hs : s = e s • e.symm 1 := by
    rw [← e.symm.map_smul]
    simp only [smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have ht : t = e t • e.symm 1 := by
    rw [← e.symm.map_smul]
    simp only [smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hs, ht, φ.map_smul]
  conv_rhs => rw [ht, hs, φ.map_smul]
  simp only [smul_eq_mul, smul_smul]
  congr 1
  ring

variable {X : Scheme.{u}} {M : X.Modules}

/-- A trivialization supplies linear coordinates on every smaller open. -/
def lineSectionsCoordinate {U V : X.Opens} (e : M.restrict U.ι ≅ structureModule U.toScheme)
    (h : V ≤ U) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) := by
  let W := U.ι ⁻¹ᵁ V
  have hV : U.ι ''ᵁ W = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr h]
  let a : Γ(M, U.ι ''ᵁ W) →ₗ[Γ(X, U.ι ''ᵁ W)] Γ(X, U.ι ''ᵁ W) :=
    { toFun := e.hom.app W
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        have hs := e.hom.app_smul r s
        change e.hom.app W (((M.restrict U.ι).smul r).hom s) =
          r * (show Γ(X, U.ι ''ᵁ W) from e.hom.app W s) at hs
        rw [moduleDual_restrict_smul] at hs
        exact hs }
  have a := LinearEquiv.ofBijective a (ConcreteCategory.bijective_of_isIso (e.hom.app W))
  exact hV ▸ a

/-- Actual dual evaluation on a line satisfies the balanced contraction identity. -/
lemma lineSheafEvaluation_balance (hM : LocallyFreeRankOne M) (U : X.Opens)
    (φ : Γ(moduleSheafDual M, U)) (s t : Γ(M, U)) :
    moduleDualEval M U φ s • t = moduleDualEval M U φ t • s := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := hM x
  refine ⟨U ⊓ V, inf_le_left, ⟨hx, hxV⟩, ?_⟩
  erw [Scheme.Modules.map_smul, Scheme.Modules.map_smul]
  rw [← moduleDualEval_restrict M inf_le_left, ← moduleDualEval_restrict M inf_le_left]
  exact linearFunctional_balance (lineSectionsCoordinate e inf_le_right) _ _ _

end FLT.Mazur.FCurve
