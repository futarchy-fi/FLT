/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalKernelCoverExtension
public import FLT.Mazur.WeierstrassLocalNodalTransport
public import FLT.Mazur.EllipticSplitDepthExtension

/-!
# Split depth for a covered original local kernel

Construct a split-depth model of the original cubic and transport the entire
kernel cover to it. Both original generic variable changes survive, including
the new integral normalization on the source and the original quotient target.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve IsLocalRing
namespace FLT.Mazur.WeierstrassLocalKernelSplitDepthModel
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  (E V : WeierstrassCurve R) [E.IsElliptic]
  (W U : WeierstrassCurve A) (C D : VariableChange K)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))
  (hD : D • V.map (algebraMap R K) = U.map (algebraMap A K))
  {H : Scheme} (i : H ⟶ integralCurve E)
  {m : ℕ} (r : Fin m → (Spec (.of K) ⟶ localGenericKernel E W C hC i))
  (hr : ∀ a, r a ≫ localGenericKernelInclusion E W C hC i ≫
    integralCurveStructure (W.map (algebraMap A K)) = 𝟙 _)
  (hi : ∀ a, IsOpenImmersion (r a))
  (hc : ∀ x : localGenericKernel E W C hC i, ∃ a z, r a z = x)

include hD hr hi hc in
/-- Construct depth and a full cover on one model, retaining both original generic equations. -/
theorem exists_model (hΔ : W.Δ ∈ maximalIdeal A) (h4 : IsUnit W.c₄) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (B : ValuationSubring L) (_ : IsDiscreteValuationRing B)
      (_ : PerfectField (ResidueField B)) (φ : A →+* B) (T : VariableChange B)
      (n : ℕ) (π : A)
      (hC' : (T.map (algebraMap B L) * C.map (algebraMap K L)) •
        E.map (algebraMap R L) = (T • W.map φ).map (algebraMap B L))
      (_hD' : D.map (algebraMap K L) • V.map (algebraMap R L) =
        (U.map φ).map (algebraMap B L))
      (r' : Fin m → (Spec (.of L) ⟶ localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i)),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧ Module.finrank K L ≤ 2 ∧ T.u = 1 ∧
      W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
      SplitNodeDepth (T • W.map φ) (φ π) n ∧
      (∀ a, r' a ≫ localGenericKernelInclusion E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i ≫
          integralCurveStructure ((T • W.map φ).map (algebraMap B L)) = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r' a)) ∧
      (∀ x : localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i,
        ∃ a z, r' a z = x) := by
  let _ : (W.map (algebraMap A K)).IsElliptic := by rw [← hC]; infer_instance
  obtain ⟨n, π, hd, hd', L, field, alg, fin, sep, B, dvr, perf, φ, T,
      loc, hφ, hB, rank, hT, depth⟩ := exists_splitDepth_extension A W hΔ h4
  let _ := field
  let _ := alg
  let _ := fin
  let _ := sep
  let _ := dvr
  let _ := perf
  let _ := loc
  let _ : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let _ : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have he : (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K) :=
    WeierstrassLocalCoefficientExtension.compatibility_of_apply φ hφ
  have hC' := WeierstrassLocalNodalTransport.normalized_changeEquation φ W he E C hC T
  have hD' := WeierstrassLocalCoefficientExtension.changeEquation φ he V U D hD
  let C' := T.map (algebraMap B L) * C.map (algebraMap K L)
  let r' := fun a ↦ WeierstrassLocalKernelCoverExtension.sectionMap
    E W (T • W.map φ) C C' hC hC' i (r a) (hr a)
  refine ⟨L, field, alg, inferInstance, inferInstance, fin, sep, B, dvr, perf, φ,
    T, n, π, hC', hD', r', loc, hφ, hB, rank, hT, hd, hd', depth, ?_, ?_, ?_⟩
  · intro a
    exact WeierstrassLocalKernelCoverExtension.sectionMap_structure
      E W (T • W.map φ) C C' hC hC' i (r a) (hr a)
  · intro a
    let _ := hi a
    exact WeierstrassLocalKernelCoverExtension.sectionMap_isOpenImmersion
      E W (T • W.map φ) C C' hC hC' i (r a) (hr a)
  · exact WeierstrassLocalKernelCoverExtension.sectionMap_covers
      E W (T • W.map φ) C C' hC hC' i r hr hc

end FLT.Mazur.WeierstrassLocalKernelSplitDepthModel
