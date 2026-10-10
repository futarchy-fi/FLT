/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechZeroCoordinates
public import FLT.Mazur.CohomologicallyFlatSections

/-!
# Canonical normalization of the Cech section comparison

The geometric zero-cycle comparison is the actual pullback-unit map on
sections. Thus the construction remembers the canonical map, not only an
abstract isomorphism of section modules.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules)

/-- The canonical map on global sections, with both structural base actions. -/
def globalComparison :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom ⊤ →ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj M) q.appTop.hom ⊤ :=
  (CartesianOpenSectionMap.comparison h M ⊤).hom

/-- On pure tensors the canonical map is scalar multiplication of section pullback. -/
lemma globalComparison_tmul (b : Γ(T, ⊤)) (s : baseSections M f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    globalComparison h M (b ⊗ₜ[Γ(S, ⊤)] s) =
      b • (show baseSections ((pullback p).obj M) q.appTop.hom ⊤ from pullGlobal p M s) :=
  CartesianOpenSectionMap.comparison_tmul h M ⊤ b s

variable [IsAffine T] [IsAffine S] [X.IsSeparated] [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- Geometric zero-cycle coordinates agree with the canonical pullback of a section. -/
lemma geometricTermEquiv_zero_tmul (b : Γ(T, ⊤)) (s : baseSections M f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    geometricTermEquiv h M U hU 0
        (b ⊗ₜ[Γ(S, ⊤)] (baseSectionsZeroKernelEquiv M U f.appTop.hom hCover s).val) =
      (baseSectionsZeroKernelEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
        q.appTop.hom (p.iSup_preimage_eq_top hCover)
          (globalComparison h M (b ⊗ₜ[Γ(S, ⊤)] s))).val := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply (baseTermCoordinates ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom 0).injective
  funext a
  change baseTermCoordinates _ _ _ 0 (chartTermEquiv p q M U 0
    (termComparison h M U 0 _)) a = _
  rw [chartTermEquiv_apply]
  change baseRestriction _ _ _ (termComparison h M U 0 _ a) = _
  rw [termComparison_tmul, baseSectionsZeroKernelEquiv_apply]
  rw [← CartesianOpenSectionMap.comparison_tmul h M (V U 0 a.val)]
  have hc := CartesianSectionRestriction.comparison_lTensor h M
    (show V U 0 a.val ≤ ⊤ from le_top) (b ⊗ₜ[Γ(S, ⊤)] s)
  change CartesianOpenSectionMap.comparison h M (V U 0 a.val)
    (b ⊗ₜ[Γ(S, ⊤)] (baseRestriction M f.appTop.hom le_top s)) = _ at hc
  rw [hc]
  change ((baseRestriction _ _ _).comp (baseRestriction _ _ _)) _ = _
  rw [baseRestriction_comp]
  exact (baseSectionsZeroKernelEquiv_apply ((pullback p).obj M)
    (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (p.iSup_preimage_eq_top hCover) _ a).symm

variable [∀ n, Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n)]
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom M (n + 1)))

/-- The constructed universal equivalence is the canonical section map on pure tensors. -/
lemma cohomologicallyFlatSectionsEquiv_tmul (b : Γ(T, ⊤))
    (s : baseSections M f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    cohomologicallyFlatSectionsEquiv h M U hU hCover hH (b ⊗ₜ[Γ(S, ⊤)] s) =
      globalComparison h M (b ⊗ₜ[Γ(S, ⊤)] s) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply (baseSectionsZeroKernelEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom (p.iSup_preimage_eq_top hCover)).injective
  change (baseSectionsZeroKernelEquiv _ _ _ (p.iSup_preimage_eq_top hCover))
    ((baseSectionsZeroKernelEquiv _ _ _ (p.iSup_preimage_eq_top hCover)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change geometricTermEquiv h M U hU 0
    (b ⊗ₜ[Γ(S, ⊤)] (baseSectionsZeroKernelEquiv M U f.appTop.hom hCover s).val) = _
  exact geometricTermEquiv_zero_tmul h M U hU hCover b s

/-- The equivalence agrees with the canonical map on every tensor. -/
lemma cohomologicallyFlatSectionsEquiv_eq :
    (cohomologicallyFlatSectionsEquiv h M U hU hCover hH).toLinearMap =
      globalComparison h M := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b s => exact cohomologicallyFlatSectionsEquiv_tmul h M U hU hCover hH b s
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.IncreasingCechCoefficients
