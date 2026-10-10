/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCoefficientReindex
public import FLT.Mazur.IncreasingCechZeroSections

/-!
# Tensor kernels as actual sections after affine base change

Finite affine chart comparison and sheaf gluing identify the degree-zero kernel
of the tensorized bounded complex with global sections on the actual cartesian
scheme. The change of base need not be flat.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCoefficients
open Scheme.Modules hiding map_smul
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  [IsAffine T] [IsAffine S] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- The tensorized differential with its coefficient-ring linearity. -/
def tensorD (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm M U f.appTop.hom n →ₗ[Γ(T, ⊤)]
      Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm M U f.appTop.hom (n + 1) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
    (baseD M U f.appTop.hom n)

/-- Every tensor term is the actual bounded term on the inverse-image cover. -/
def geometricTermEquiv (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm M U f.appTop.hom n ≃ₗ[Γ(T, ⊤)]
      BaseTerm ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n :=
  (LinearEquiv.ofBijective (termComparison h M U n) (termComparison_bijective h M U hU n)).trans
    (chartTermEquiv p q M U n)

/-- The term equivalence intertwines the two actual differentials. -/
lemma geometricTermEquiv_d (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ x, geometricTermEquiv h M U hU (n + 1) (tensorD (f := f) (g := g) M U n x) =
      baseD ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
        (geometricTermEquiv h M U hU n x) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro x
  change chartTermEquiv p q M U (n + 1)
    (termComparison h M U (n + 1) ((baseD M U f.appTop.hom n).lTensor
      Γ(T, ⊤) x)) = _
  rw [termComparison_d, chartTermEquiv_d]
  rfl

/-- The tensor kernel identifies with actual bounded cycles after base change. -/
def geometricKernelEquiv (n : ℕ) :
    (tensorD (f := f) (g := g) M U n).ker ≃ₗ[Γ(T, ⊤)]
      (baseD ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n).ker := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let e := geometricTermEquiv h M U hU n
  refine (e.submoduleMap (tensorD (f := f) (g := g) M U n).ker).trans
    (LinearEquiv.ofEq _ _ ?_)
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  change tensorD (f := f) (g := g) M U n (e.symm y) = 0 ↔ _
  rw [← (geometricTermEquiv h M U hU (n + 1)).map_eq_zero_iff, geometricTermEquiv_d]
  change baseD ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
    (e (e.symm y)) = 0 ↔ _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Actual sheaf gluing identifies the tensor zero-kernel with cartesian global sections. -/
def tensorKernelSectionsEquiv (hCover : iSup U = ⊤) :
    (tensorD (f := f) (g := g) M U 0).ker ≃ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj M) q.appTop.hom ⊤ :=
  (geometricKernelEquiv h M U hU 0).trans
    (baseSectionsZeroKernelEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom
      (p.iSup_preimage_eq_top hCover)).symm

end FLT.Mazur.IncreasingCechCoefficients
