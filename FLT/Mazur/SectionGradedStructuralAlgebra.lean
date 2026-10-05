/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedBaseChangeMultiplication
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Structural scalars on the full section ring

The algebra over the base scheme uses the existing module action on every
homogeneous summand. Its scalar extension has the usual tensor product ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings TensorProduct
namespace FLT.Mazur.SectionGradedBaseChange
open FCurve OpenModuleSectionScalars SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)

/-- The section module carries the tensor-power section ring. -/
instance structuralRing : Ring (sectionModule f L) :=
  inferInstanceAs (Ring (SectionGradedSum.Sections L ⊤))

/-- A line bundle gives a commutative ring over the structural base. -/
instance structuralCommRing [Fact (LocallyFreeRankOne L)] : CommRing (sectionModule f L) :=
  inferInstanceAs (CommRing (SectionGradedSum.Sections L ⊤))

/-- The structural action agrees with the structure-sheaf action on the full sum. -/
lemma structural_smul (r : Γ(S, ⊤)) (s : sectionModule f L) :
    r • s = (f.appTop r) • (s : SectionGradedSum.Sections L ⊤) := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    simp only [← DirectSum.of_smul]
    change DirectSum.of (SectionGradedMultiplication.Piece L ⊤) n
      (r • (s : openSections f _ ⊤)) =
        DirectSum.of (SectionGradedMultiplication.Piece L ⊤) n ((f.appTop r) • s)
    congr 1
    change (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
      (f.appTop r)) • s = (f.appTop r) • s
    rw [show homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤) = 𝟙 _ from rfl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  | add a b ha hb => simp only [smul_add, ha, hb]

/-- The structural algebra retains the previously defined base module action. -/
instance structuralAlgebra : Algebra Γ(S, ⊤) (sectionModule f L) :=
  @Algebra.ofModule Γ(S, ⊤) (sectionModule f L) _ _ (sectionModule f L).isModule
    (fun r a b ↦ by
      rw [structural_smul f L r a, structural_smul f L r (a * b)]
      exact @smul_mul_assoc Γ(X, ⊤) (SectionGradedSum.Sections L ⊤) _ _ _ (f.appTop r) a b)
    (fun r a b ↦ by
      rw [structural_smul f L r b, structural_smul f L r (a * b)]
      exact @mul_smul_comm Γ(X, ⊤) (SectionGradedSum.Sections L ⊤) _ _ _ (f.appTop r) a b)

/-- Scalars enter the section ring in degree zero by the structural pullback. -/
lemma structural_algebraMap (r : Γ(S, ⊤)) :
    algebraMap Γ(S, ⊤) (sectionModule f L) r = of L ⊤ 0 (f.appTop r) := by
  rw [Algebra.algebraMap_eq_smul_one, structural_smul]
  change (f.appTop r) • (of L ⊤ 0 (1 : Γ(X, ⊤))) = _
  rw [← _root_.map_smul]
  simp

variable {T : Scheme} (g : T ⟶ S)

/-- Scalar extension uses the usual tensor product ring structure. -/
instance extendedRing : Ring ((ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) := by
  exact @Algebra.TensorProduct.instRing Γ(S, ⊤) Γ(T, ⊤) (sectionModule f L)
    _ _ g.appTop.hom.toAlgebra _ (structuralAlgebra f L)

/-- For a line bundle the scalar extension is a commutative tensor product ring. -/
instance extendedCommRing [Fact (LocallyFreeRankOne L)] :
    CommRing ((ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact Algebra.TensorProduct.instCommRing (R := Γ(S, ⊤)) (A := Γ(T, ⊤))
    (B := sectionModule f L)

/-- The tensor product algebra retains the scalar extension's existing module action. -/
instance extendedAlgebra :
    Algebra Γ(T, ⊤) ((ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact Algebra.TensorProduct.leftAlgebra (R := Γ(S, ⊤)) (S := Γ(T, ⊤))
    (A := Γ(T, ⊤)) (B := sectionModule f L)

end FLT.Mazur.SectionGradedBaseChange
