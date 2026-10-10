/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiberCohomologyTensorExactness

/-!
# Detecting actual fiber cohomology by the original tensor complex

The cartesian comparison works in both directions. Positive exactness of the
original Cech complex with coefficient-algebra tensors is equivalent to
vanishing of the actual pulled-back sheaf cohomology, without flat coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve Chow

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include h hU hCover in
/-- Exactness of the coefficient complex kills actual pulled-back cohomology in that degree. -/
theorem pullback_vanishing_of_tensor_exact (n : ℕ)
    (ht : let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      Function.Exact ((baseD M U f.appTop.hom n).lTensor Γ(T, ⊤))
        ((baseD M U f.appTop.hom (n + 1)).lTensor Γ(T, ⊤))) :
    Subsingleton (ModuleH ((pullback p).obj M) (n + 1)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have hm : ((positiveModuleComplex M U f.appTop.hom n).map
      (ModuleCat.extendScalars g.appTop.hom)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact (ht x).mp hx
  have hp := ShortComplex.exact_of_iso (geometricPositiveComplexIso h M U hU n) hm
  let _ := ModuleCat.subsingleton_of_isZero
    ((ShortComplex.exact_iff_isZero_homology _).mp hp)
  let _ := (positiveModuleHomologyEquiv ((pullback p).obj M)
    (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n).symm.injective.subsingleton
  let _ : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
  let _ : P.IsSeparated := ⟨by
    simpa only [Limits.terminal.comp_from] using
      (inferInstance : IsSeparated (p ≫ Limits.terminal.from X))⟩
  let _ := QuasiCoherentSchemePullback.isQuasicoherent p M
  let e : BaseHomology ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (n + 1) ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom ((pullback p).obj M) (n + 1) :=
    affineRingCohomologyEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
      (fun i ↦ (hU i).preimage p) (p.iSup_preimage_eq_top hCover) q.appTop.hom (n + 1)
  exact e.symm.injective.subsingleton

omit [IsAffine T] in
include hU hCover in
/-- Coefficient-algebra tensor exactness is precisely actual geometric positive vanishing. -/
theorem coefficient_exact_iff_geometric_vanishing
    (B : Type) [CommRing B] [Algebra Γ(S, ⊤) B] :
    (∀ n, Function.Exact ((baseD M U f.appTop.hom n).lTensor B)
      ((baseD M U f.appTop.hom (n + 1)).lTensor B)) ↔
    ∀ n, Subsingleton (ModuleH
      ((pullback (Limits.pullback.fst f (AffineBaseChangeCoefficients.baseMap S B))).obj M)
        (n + 1)) := by
  refine ⟨fun ht n ↦ ?_, fun hV n ↦
    coefficient_exact_of_geometric_vanishing M U hU hCover B hV n⟩
  let g := AffineBaseChangeCoefficients.baseMap S B
  let _ : Algebra Γ(S, ⊤) Γ(Spec (.of B), ⊤) := g.appTop.hom.toAlgebra
  apply pullback_vanishing_of_tensor_exact (IsPullback.of_hasPullback f g) M U hU hCover n
  exact (lTensor_exact_iff_coefficients (AffineBaseChangeCoefficients.coefficientEquiv S B)
    (baseD M U f.appTop.hom n) (baseD M U f.appTop.hom (n + 1))).mpr (ht n)

end FLT.Mazur.IncreasingCechCoefficients
