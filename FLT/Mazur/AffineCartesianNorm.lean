/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianSectionPushout
public import FLT.Mazur.FiniteFreeTranslationNorm

/-!
# Norm base change for arbitrary affine cartesian squares

The entire original section algebra is transported through the section pushout.
A finite basis belongs to the original morphism, with no product envelope or
translation presentation required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.AffineCartesianNorm
universe u v
set_option backward.isDefEq.respectTransparency false
variable {P X T Y : Scheme.{u}} [IsAffine X] [IsAffine T] [IsAffine Y]
  (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
  (H : IsPullback a b f g)
set_option quotPrecheck false
local notation "B" => Γ(Y, ⊤)
local notation "C" => Γ(X, ⊤)
local notation "S" => Γ(T, ⊤)
local notation "D" => Γ(P, ⊤)

/-- Tensor coordinates of the full cartesian source, over its original target. -/
def tensorIso :
    let _ := f.appTop.hom.toAlgebra
    let _ := g.appTop.hom.toAlgebra
    CommRingCat.of (S ⊗[B] C) ≅ D := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  exact (CommRingCat.isPushout_tensorProduct B S C).isoIsPushout
    _ _ (isPushout_appTop_of_isPullback H).flip

/-- Target coefficients are pulled back along the actual changed morphism. -/
theorem tensorIso_left (t : S) :
    let _ := f.appTop.hom.toAlgebra
    let _ := g.appTop.hom.toAlgebra
    (tensorIso a b f g H).hom (t ⊗ₜ[B] 1) = b.appTop t := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  exact congrArg (fun h : S ⟶ D ↦ h t)
    (IsPushout.inl_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct B S C)
      (isPushout_appTop_of_isPullback H).flip)

/-- Original source sections are pulled back without deleting any branches. -/
theorem tensorIso_right (s : C) :
    let _ := f.appTop.hom.toAlgebra
    let _ := g.appTop.hom.toAlgebra
    (tensorIso a b f g H).hom (1 ⊗ₜ[B] s) = a.appTop s := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  exact congrArg (fun h : C ⟶ D ↦ h s)
    (IsPushout.inr_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct B S C)
      (isPushout_appTop_of_isPullback H).flip)

/-- The section pushout is an algebra equivalence over the changed target. -/
def tensorAlgEquiv :
    let _ := f.appTop.hom.toAlgebra
    let _ := g.appTop.hom.toAlgebra
    let _ := b.appTop.hom.toAlgebra
    (S ⊗[B] C) ≃ₐ[S] D := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  exact { (tensorIso a b f g H).commRingCatIsoToRingEquiv with
    commutes' := tensorIso_left a b f g H }

variable {ι : Type v} [Finite ι]

/-- A basis of the original map gives a basis of the whole changed source. -/
def sectionBasis :
    let _ := f.appTop.hom.toAlgebra
    let _ := b.appTop.hom.toAlgebra
    Basis ι B C → Basis ι S D := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact (basis.baseChange S).map (tensorAlgEquiv a b f g H).toLinearEquiv

include H in
/-- Norms of original sections commute with any affine cartesian change of target. -/
theorem norm_pullback :
    let _ := f.appTop.hom.toAlgebra
    let _ := b.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι B C) (s : C),
    Algebra.norm S (a.appTop s) = g.appTop (Algebra.norm B s) := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  rw [← tensorIso_right a b f g H]
  exact FiniteFreeTranslationNorm.norm_baseChange_equiv basis S
    (tensorAlgEquiv a b f g H) s

end FLT.Mazur.AffineCartesianNorm
