/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLocalCoordinates
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Commutativity for line-bundle section rings

Open trivializations detect equality of the two multiplication morphisms.
The resulting commutative ring contains every section of every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedMultiplication
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L : X.Modules}

/-- Tensor-degree addition commutes with symmetry for a line bundle. -/
lemma addIso_comm (hL : LocallyFreeRankOne L) (m n : ℕ) :
    (tensorPowerAddIso L m n).hom =
      (ModuleSheafTensorAssociator.comm (tensorPower L m) (tensorPower L n)).hom ≫
        (tensorPowerAddIso L n m).hom ≫
          (eqToIso (congrArg (tensorPower L) (Nat.add_comm n m))).hom := by
  choose W hW e using hL
  have hcover : iSup W = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hW x⟩
  apply ModuleSheafMorphismGluing.hom_ext_restrict W hcover
  intro x
  apply restrict_hom_ext (W x).ι
  intro V s t
  change (tensorPowerAddIso L m n).hom.app ((W x).ι ''ᵁ V) (pure _ _ _ s t) =
    (eqToIso (congrArg (tensorPower L) (Nat.add_comm n m))).hom.app ((W x).ι ''ᵁ V)
      ((tensorPowerAddIso L n m).hom.app ((W x).ι ''ᵁ V)
        ((ModuleSheafTensorAssociator.comm _ _).hom.app ((W x).ι ''ᵁ V)
          (pure _ _ _ s t)))
  rw [ModuleSheafTensorAssociator.comm_hom_pure]
  change mul L ((W x).ι ''ᵁ V) m n s t =
    cast L (Nat.add_comm n m) ((W x).ι ''ᵁ V) (mul L ((W x).ι ''ᵁ V) n m t s)
  apply SectionGradedLocalCoordinates.coordinate_injective (e x).some (m + n) V
  rw [SectionGradedLocalCoordinates.coordinate_cast,
    SectionGradedLocalCoordinates.coordinate_mul,
    SectionGradedLocalCoordinates.coordinate_mul, _root_.mul_comm]

/-- Arbitrary local sections of line-bundle powers commute under multiplication. -/
lemma mul_comm (hL : LocallyFreeRankOne L) (m n : ℕ) (U : X.Opens)
    (s : Piece L U m) (t : Piece L U n) :
    mul L U m n s t = cast L (Nat.add_comm n m) U (mul L U n m t s) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (addIso_comm hL m n)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensorAssociator.comm_hom_pure] at h
  exact h

end FLT.Mazur.SectionGradedMultiplication

namespace FLT.Mazur.SectionGradedSum
open SectionGradedMultiplication FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- Line bundles give a commutative graded ring of tensor-power sections. -/
instance gradedCommRing [hL : Fact (LocallyFreeRankOne L)] :
    DirectSum.GCommRing (Piece L U) where
  __ := gradedRing L U
  mul_comm := by
    rintro ⟨m, s⟩ ⟨n, t⟩
    change (⟨m + n, mul L U m n s t⟩ : GradedMonoid (Piece L U)) =
      ⟨n + m, mul L U n m t s⟩
    rw [SectionGradedMultiplication.mul_comm hL.out]
    exact sigma_cast L U _ _

/-- The full section ring of a line bundle is commutative. -/
instance lineSectionCommRing [Fact (LocallyFreeRankOne L)] :
    CommRing (Sections L U) := DirectSum.commRing _

/-- The original bilinear product commutes for any line bundle. -/
lemma product_comm (hL : LocallyFreeRankOne L) (a b : Sections L U) :
    product L U a b = product L U b a := by
  have : Fact (LocallyFreeRankOne L) := ⟨hL⟩
  simp only [← mul_eq_product, _root_.mul_comm]

end FLT.Mazur.SectionGradedSum
