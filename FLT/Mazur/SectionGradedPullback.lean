/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAlgebra

/-!
# Pullback preserves tensor-degree multiplication

The comparison is the actual tensor-power pullback isomorphism, evaluated
on the adjunction unit. Compatibility is proved on sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedPullback
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)

/-- The adjoint of the canonical tensor-power comparison. -/
def powerMap (n : ℕ) : tensorPower L n ⟶
    (pushforward f).obj (tensorPower ((pullback f).obj L) n) :=
  (pullbackPushforwardAdjunction f).homEquiv _ _ (tensorPowerIso f L n).hom

/-- Pull a section back to the inverse-image open and compare tensor powers. -/
def pull (n : ℕ) (U : Y.Opens) (s : Piece L U n) :
    Piece ((pullback f).obj L) (f ⁻¹ᵁ U) n := (powerMap f L n).app U s

/-- Degree transport commutes with pullback. -/
lemma pull_cast {m n : ℕ} (h : m = n) (U : Y.Opens) (s : Piece L U m) :
    pull f L n U (cast L h U s) = cast ((pullback f).obj L) h (f ⁻¹ᵁ U)
      (pull f L m U s) := by
  subst n
  rfl

/-- Pullback is semilinear over the actual structure-sheaf map. -/
lemma pull_smul (n : ℕ) (U : Y.Opens) (r : Γ(Y, U)) (s : Piece L U n) :
    pull f L n U (r • s) = f.app U r • pull f L n U s :=
  Hom.app_smul (powerMap f L n) r s

/-- Degree zero pulls back by the structure-sheaf map. -/
lemma pull_zero (U : Y.Opens) (r : Γ(Y, U)) :
    pull f L 0 U r = f.app U r := modulePullbackUnitIso_unit f U r

/-- Pullback preserves prepending a local tensor factor. -/
lemma pull_cons (n : ℕ) (U : Y.Opens) (s : Γ(L, U)) (t : Piece L U n) :
    pull f L (n + 1) U (cons L n U s t) =
      cons ((pullback f).obj L) n (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app L).app U s) (pull f L n U t) := by
  change (ModuleSheafTensor.map (𝟙 ((pullback f).obj L)) (tensorPowerIso f L n).hom).app
    (f ⁻¹ᵁ U) (((pullbackPushforwardAdjunction f).homEquiv _ _
      (tensorIso f L (tensorPower L n)).hom).app U (pure _ _ U s t)) = _
  rw [tensorIso_adj_pure]
  erw [ModuleSheafTensor.map_pure]
  rfl

/-- The adjoint tensor comparison evaluates the two pulled-back inputs. -/
lemma tensorComparison_pure (m n : ℕ) (U : Y.Opens)
    (s : Piece L U m) (t : Piece L U n) :
    ((pullbackPushforwardAdjunction f).homEquiv _ _
      ((tensorIso f (tensorPower L m) (tensorPower L n)).hom ≫
        ModuleSheafTensor.map (tensorPowerIso f L m).hom (tensorPowerIso f L n).hom ≫
          (tensorPowerAddIso ((pullback f).obj L) m n).hom)).app U (pure _ _ U s t) =
      mul ((pullback f).obj L) (f ⁻¹ᵁ U) m n (pull f L m U s) (pull f L n U t) := by
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app]
  rw [tensorIso_adj_pure]
  erw [ModuleSheafTensor.map_pure]
  rfl

/-- The tensor-power pullback comparison preserves addition of exponents. -/
lemma addIso_pullback (m n : ℕ) :
    (tensorPowerAddIso L m n).hom ≫ powerMap f L (m + n) =
      (pullbackPushforwardAdjunction f).homEquiv _ _
        ((tensorIso f (tensorPower L m) (tensorPower L n)).hom ≫
          ModuleSheafTensor.map (tensorPowerIso f L m).hom (tensorPowerIso f L n).hom ≫
            (tensorPowerAddIso ((pullback f).obj L) m n).hom) := by
  induction m with
  | zero =>
    apply ModuleSheafTensor.hom_ext
    intro U r s
    rw [tensorComparison_pure]
    change pull f L (0 + n) U (mul L U 0 n r s) =
      mul ((pullback f).obj L) (f ⁻¹ᵁ U) 0 n (pull f L 0 U r) (pull f L n U s)
    rw [SectionGradedMultiplication.zero_mul, pull_cast, pull_smul, pull_zero,
      SectionGradedMultiplication.zero_mul]
  | succ m ih =>
    apply ModuleSheafTensorAssociator.left_hom_ext
    intro U a b c
    have hi := congrArg (fun g ↦ g.app U (pure _ _ U b c)) ih
    rw [tensorComparison_pure] at hi
    change pull f L (m + n) U (mul L U m n b c) =
      mul ((pullback f).obj L) (f ⁻¹ᵁ U) m n (pull f L m U b) (pull f L n U c) at hi
    change pull f L (m + 1 + n) U (mul L U (m + 1) n (cons L m U a b) c) =
      ((pullbackPushforwardAdjunction f).homEquiv _ _ _).app U
        (pure (tensorPower L (m + 1)) (tensorPower L n) U (cons L m U a b) c)
    rw [tensorComparison_pure, succ_mul_pure, pull_cast, pull_cons, hi, pull_cons,
      succ_mul_pure]

/-- Multiplication of arbitrary local sections commutes with pullback. -/
lemma pull_mul (m n : ℕ) (U : Y.Opens) (s : Piece L U m) (t : Piece L U n) :
    pull f L (m + n) U (mul L U m n s t) =
      mul ((pullback f).obj L) (f ⁻¹ᵁ U) m n (pull f L m U s) (pull f L n U t) := by
  have h := congrArg (fun g ↦ g.app U (pure _ _ U s t)) (addIso_pullback f L m n)
  rw [tensorComparison_pure] at h
  exact h

end FLT.Mazur.SectionGradedPullback
