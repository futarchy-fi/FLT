/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePicardSections
public import FLT.Mazur.TildeInvertibleLocal
public import FLT.Mazur.AffineQuasiCoherentBaseChange
public import FLT.Mazur.SchemePicardPullback

/-!
# The affine Picard comparison

Global sections identify the scheme Picard group with the ring Picard group.
The identification commutes with arbitrary morphisms of affine schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.SchemePicard

open FCurve AffineModuleGlobalSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- The global sections of affine tilde recover the original invertible module class. -/
theorem sectionsClass_affineTilde (N : ModuleCat Γ(X, ⊤)) [Module.Invertible Γ(X, ⊤) N] :
    sectionsClass ((affineTilde X).obj N) (affineTilde_locallyFreeRankOne X N) =
      CommRing.Pic.mk Γ(X, ⊤) N := by
  have := sections_invertible _ (affineTilde_locallyFreeRankOne X N)
  exact CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨(asIso ((affineAdjunction X).unit.app N)).symm.toLinearEquiv⟩

/-- Every invertible ring module class comes from a line bundle on the affine scheme. -/
theorem sectionsHom_surjective : Function.Surjective (sectionsHom X) := by
  intro a
  refine ⟨mk ((affineTilde X).obj (ModuleCat.of Γ(X, ⊤) a))
    (affineTilde_locallyFreeRankOne X _), ?_⟩
  rw [sectionsHom_mk, sectionsClass_affineTilde, CommRing.Pic.mk_eq_self]

/-- The affine Picard group equivalence, defined by actual global sections. -/
def affineEquiv (X : Scheme.{u}) [IsAffine X] : Pic X ≃* CommRing.Pic Γ(X, ⊤) :=
  MulEquiv.ofBijective (sectionsHom X) ⟨sectionsHom_injective, sectionsHom_surjective⟩

/-- The equivalence sends a line bundle to the class of its section module. -/
@[simp]
theorem affineEquiv_mk (M : X.Modules) (hM : LocallyFreeRankOne M) :
    affineEquiv X (mk M hM) = sectionsClass M hM := rfl

/-- The inverse comparison is represented by affine tilde. -/
theorem affineEquiv_symm_mk (N : ModuleCat Γ(X, ⊤)) [Module.Invertible Γ(X, ⊤) N] :
    (affineEquiv X).symm (CommRing.Pic.mk Γ(X, ⊤) N) =
      mk ((affineTilde X).obj N) (affineTilde_locallyFreeRankOne X N) := by
  apply (affineEquiv X).injective
  rw [MulEquiv.apply_symm_apply, affineEquiv_mk, sectionsClass_affineTilde]

/-- The global-section comparison commutes with pullback between affine schemes. -/
theorem sectionsHom_pullback (f : X ⟶ Y) (a : Pic Y) :
    sectionsHom X (pullback f a) =
      CommRing.Pic.mapRingHom f.appTop.hom (sectionsHom Y a) := by
  induction a using inductionOn with | h M hM =>
    have := rankOne_finitePresentation M hM
    have := sections_invertible M hM
    have := sections_invertible _ (hM.pullback f)
    let := f.appTop.hom.toAlgebra
    change CommRing.Pic.mk Γ(X, ⊤) Γ((Scheme.Modules.pullback f).obj M, ⊤) =
      CommRing.Pic.mk Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(Y, ⊤)] (CommRing.Pic.mk Γ(Y, ⊤) Γ(M, ⊤)))
    apply CommRing.Pic.mk_eq_mk_iff.mpr
    let e : Γ((Scheme.Modules.pullback f).obj M, ⊤) ≃ₗ[Γ(X, ⊤)]
        Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(M, ⊤) :=
      (AffineQuasiCoherentBaseChange.sectionsIso f M).symm.toLinearEquiv
    exact ⟨e.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (CommRing.Pic.mk.linearEquiv Γ(Y, ⊤) Γ(M, ⊤)).symm)⟩

/-- Naturality of the affine Picard equivalence. -/
theorem affineEquiv_pullback (f : X ⟶ Y) (a : Pic Y) :
    affineEquiv X (pullback f a) =
      CommRing.Pic.mapRingHom f.appTop.hom (affineEquiv Y a) :=
  sectionsHom_pullback f a

end FLT.Mazur.SchemePicard
