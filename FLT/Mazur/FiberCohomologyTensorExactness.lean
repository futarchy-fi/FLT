/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicCoefficientCohomology
public import FLT.Mazur.AffineBaseChangeCoefficients

/-!
# From actual fiber cohomology to tensor exactness

The cartesian Cech comparison turns vanishing of actual pulled-back sheaf
cohomology into exactness of the coefficient complex. Spectrum coordinates
then recover the original coefficient algebra without assuming flatness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve Chow

section Coefficients
variable {R A B M N P : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Tensor exactness is invariant under a linear change of coefficient coordinates. -/
lemma lTensor_exact_iff_coefficients (c : A ≃ₗ[R] B) (d : M →ₗ[R] N) (e : N →ₗ[R] P) :
    Function.Exact (d.lTensor A) (e.lTensor A) ↔
      Function.Exact (d.lTensor B) (e.lTensor B) := by
  let a := TensorProduct.congr c (LinearEquiv.refl R M)
  let b := TensorProduct.congr c (LinearEquiv.refl R N)
  let t := TensorProduct.congr c (LinearEquiv.refl R P)
  apply LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (d.lTensor A) (e.lTensor A) (d.lTensor B) (e.lTensor B)
    a.toLinearMap b.toLinearMap t.toLinearMap _ _ a.surjective b.bijective t.injective
  · change (d.lTensor B).comp (c.toLinearMap.rTensor M) =
      (c.toLinearMap.rTensor N).comp (d.lTensor A)
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  · change (e.lTensor B).comp (c.toLinearMap.rTensor N) =
      (c.toLinearMap.rTensor P).comp (e.lTensor A)
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
end Coefficients

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include h hU hCover in
/-- Vanishing of actual geometric cohomology gives tensor exactness over spectrum sections. -/
theorem tensor_exact_of_pullback_vanishing
    (hV : ∀ n, Subsingleton (ModuleH ((pullback p).obj M) (n + 1))) (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Function.Exact ((baseD M U f.appTop.hom n).lTensor Γ(T, ⊤))
      ((baseD M U f.appTop.hom (n + 1)).lTensor Γ(T, ⊤)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
  let _ : P.IsSeparated := ⟨by
    simpa only [Limits.terminal.comp_from] using
      (inferInstance : IsSeparated (p ≫ Limits.terminal.from X))⟩
  let _ := QuasiCoherentSchemePullback.isQuasicoherent p M
  have hp := acyclic_positiveModuleComplex_exact (f := q) ((pullback p).obj M)
    (fun i ↦ p ⁻¹ᵁ U i) (fun i ↦ (hU i).preimage p) (p.iSup_preimage_eq_top hCover) hV n
  have ht := ShortComplex.exact_of_iso (geometricPositiveComplexIso h M U hU n).symm hp
  dsimp only
  intro x
  constructor
  · intro hx
    exact (ShortComplex.moduleCat_exact_iff _).mp ht x hx
  · rintro ⟨y, rfl⟩
    have hz : ((baseD M U f.appTop.hom (n + 1)).lTensor Γ(T, ⊤)).comp
        ((baseD M U f.appTop.hom n).lTensor Γ(T, ⊤)) = 0 := by
      rw [← LinearMap.lTensor_comp, baseD_comp, LinearMap.lTensor_zero]
    exact LinearMap.congr_fun hz y

omit [IsAffine T] in
include hU hCover in
/-- Actual cohomology on the coefficient-algebra fiber detects the original tensor complex. -/
theorem coefficient_exact_of_geometric_vanishing
    (B : Type) [CommRing B] [Algebra Γ(S, ⊤) B]
    (hV : ∀ n, Subsingleton (ModuleH
      ((pullback (Limits.pullback.fst f (AffineBaseChangeCoefficients.baseMap S B))).obj M)
        (n + 1))) (n : ℕ) :
    Function.Exact ((baseD M U f.appTop.hom n).lTensor B)
      ((baseD M U f.appTop.hom (n + 1)).lTensor B) := by
  let g := AffineBaseChangeCoefficients.baseMap S B
  let _ : Algebra Γ(S, ⊤) Γ(Spec (.of B), ⊤) := g.appTop.hom.toAlgebra
  have ht := tensor_exact_of_pullback_vanishing (IsPullback.of_hasPullback f g)
    M U hU hCover hV n
  exact (lTensor_exact_iff_coefficients (AffineBaseChangeCoefficients.coefficientEquiv S B)
    (baseD M U f.appTop.hom n) (baseD M U f.appTop.hom (n + 1))).mp ht

end FLT.Mazur.IncreasingCechCoefficients
