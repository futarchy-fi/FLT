/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedStructuralAlgebra

/-!
# Algebra base change for the full section ring

The existing flat affine module comparison is multiplicative on all sections,
by tensor and direct-sum induction, and hence is an algebra equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings TensorProduct
namespace FLT.Mazur.SectionGradedBaseChange
open FCurve ModuleLineBundleTensorPullback OpenModuleSectionScalars
open LinePowerSectionBaseChange SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- On a homogeneous tensor the full comparison is the degreewise comparison. -/
lemma sectionsIso_tmul_of (n : ℕ) (b : Γ(T, ⊤)) (s : Γ(tensorPower L n, ⊤)) :
    (sectionsIso h L hL).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] of L ⊤ n s) =
      of ((pullback p).obj L) ⊤ n
        ((degreeIso h L hL n).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s)) := by
  rw [degreeIso_tmul]
  exact sectionsIso_tmul_lof h L hL n b s

/-- The full comparison sends the tensor-product unit to the section-ring unit. -/
lemma sectionsIso_one : (sectionsIso h L hL).hom 1 = 1 := by
  change (sectionsIso h L hL).hom
    ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] of L ⊤ 0 (1 : Γ(X, ⊤))) = _
  rw [sectionsIso_tmul_of, degreeIso_tmul_one]
  rfl

/-- Multiplicativity for scalar tensors of arbitrary homogeneous sections. -/
lemma sectionsIso_tmul_of_mul (m n : ℕ) (b c : Γ(T, ⊤))
    (s : Γ(tensorPower L m, ⊤)) (t : Γ(tensorPower L n, ⊤)) :
    (sectionsIso h L hL).hom
      ((b * c) ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
        of L ⊤ (m + n) (SectionGradedMultiplication.mul L ⊤ m n s t)) =
      (sectionsIso h L hL).hom
        (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (show sectionModule f L from of L ⊤ m s)) *
      (sectionsIso h L hL).hom
        (c ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (show sectionModule f L from of L ⊤ n t)) := by
  rw [sectionsIso_tmul_of, sectionsIso_tmul_of, sectionsIso_tmul_of,
    mul_of, degreeIso_tmul_mul]

/-- Multiplicativity for scalar tensors without any bound on homogeneous support. -/
lemma sectionsIso_tmul_mul (b c : Γ(T, ⊤)) (s t : sectionModule f L) :
    (sectionsIso h L hL).hom ((b * c) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (s * t)) =
      (sectionsIso h L hL).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) *
        (sectionsIso h L hL).hom (c ⊗ₜ[Γ(S, ⊤),g.appTop.hom] t) := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction t using DirectSum.induction_on with
    | zero => simp
    | of n t =>
      change (sectionsIso h L hL).hom
        ((b * c) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (of L ⊤ m s * of L ⊤ n t)) = _
      rw [mul_of]
      exact sectionsIso_tmul_of_mul h L hL m n b c s t
    | add t u ht hu => simp only [mul_add, TensorProduct.tmul_add, map_add, ht, hu]
  | add s u hs hu => simp only [add_mul, TensorProduct.tmul_add, map_add, hs, hu]

/-- The full flat affine section comparison preserves multiplication. -/
lemma sectionsIso_mul
    (a b : (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :
    (sectionsIso h L hL).hom (a * b) =
      (sectionsIso h L hL).hom a * (sectionsIso h L hL).hom b := by
  induction a using TensorProduct.inductionOn with
  | tmul c s =>
    induction b using TensorProduct.inductionOn with
    | tmul d t =>
      let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      have he := Algebra.TensorProduct.tmul_mul_tmul (R := Γ(S, ⊤))
        (A := Γ(T, ⊤)) (B := sectionModule f L) c d s t
      rw [he]
      exact sectionsIso_tmul_mul h L hL c d s t
    | add b d hb hd => simp only [mul_add, map_add, hb, hd]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

/-- Flat affine base change of the full tensor-power section algebra. -/
def sectionsAlgEquiv :
    (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L) ≃ₐ[Γ(T, ⊤)]
      sectionModule q ((pullback p).obj L) :=
  AlgEquiv.ofLinearEquiv (sectionsIso h L hL).toLinearEquiv
    (sectionsIso_one h L hL) (sectionsIso_mul h L hL)

/-- The algebra equivalence is exactly the previously constructed module comparison. -/
lemma sectionsAlgEquiv_toLinearEquiv :
    (sectionsAlgEquiv h L hL).toLinearEquiv = (sectionsIso h L hL).toLinearEquiv := rfl

end FLT.Mazur.SectionGradedBaseChange
