/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalKernelPerfectSplitModel
public import FLT.Mazur.WeierstrassLocalKernelSplitDepthModel

/-!
# Constructed split depth and full cover for the original prime kernel

First split the finite kernel over a perfect-residue DVR, then normalize and
split the node. The full cover survives this second extension. Both original
cubic equations and their generic coordinate changes are retained explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart
namespace WeierstrassCurve.Velu
set_option backward.isDefEq.respectTransparency false
variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  {K : Type} [Field K] [Algebra ℚ K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  (V : WeierstrassCurve ℚ) (W U : WeierstrassCurve A) (C D : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap A K))
  (hD : D • V.map (algebraMap ℚ K) = U.map (algebraMap A K))
local notation "i" => primeKernelRationalMap E p q hq hfixed

include hC hD in
/-- Construct genuine split depth and full kernel coverage on the same original source model. -/
theorem primeLocalKernel_exists_splitDepth_model
    (hΔ : W.Δ ∈ maximalIdeal A) (h4 : IsUnit W.c₄) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra ℚ L)
      (_ : IsScalarTower ℚ K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (B : ValuationSubring L) (_ : IsDiscreteValuationRing B)
      (_ : PerfectField (ResidueField B)) (φ : A →+* B) (T : VariableChange B)
      (depth : ℕ) (π : B)
      (hC' : (T.map (algebraMap B L) * C.map (algebraMap K L)) •
        E.map (algebraMap ℚ L) = (T • W.map φ).map (algebraMap B L))
      (_hD' : D.map (algebraMap K L) • V.map (algebraMap ℚ L) =
        (U.map φ).map (algebraMap B L))
      (m : ℕ) (r : Fin m → (Spec (.of L) ⟶ localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i)),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧ T.u = 1 ∧ SplitNodeDepth (T • W.map φ) π depth ∧
      (∀ a, r a ≫ localGenericKernelInclusion E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i ≫
          integralCurveStructure ((T • W.map φ).map (algebraMap B L)) = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      (∀ x : localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i,
        ∃ a z, r a z = x) := by
  obtain ⟨M, fieldM, algKM, algQM, towerM, finM, sepM, A', dvrA', noethA', perfA',
      φ₁, hC₁, _, m, r, loc₁, hφ₁, _, hr, hi, hc⟩ :=
    primeLocalKernel_exists_perfect_split_model E p q hq hfixed A V W U C D hC hD
  let _ := fieldM
  let _ := algKM
  let _ := algQM
  let _ := towerM
  let _ := finM
  let _ := sepM
  let _ := dvrA'
  let _ := perfA'
  let _ := loc₁
  let _ : ((W.map φ₁).map (algebraMap A' M)).IsElliptic := by
    rw [← hC₁]
    infer_instance
  obtain ⟨depth, π, _, _, L, fieldL, algML, finL, sepL, B, dvrB, perfB,
      φ₂, T, loc₂, hφ₂, _, _, hT, hd⟩ := exists_splitDepth_extension A' (W.map φ₁)
    ((WeierstrassLocalNodalTransport.discriminant_mem_iff φ₁ W).mpr hΔ)
    ((WeierstrassLocalNodalTransport.c₄_isUnit_iff φ₁ W).mpr h4)
  let _ := fieldL
  let _ := algML
  let _ := finL
  let _ := sepL
  let _ := dvrB
  let _ := perfB
  let _ := loc₂
  let _ : Algebra K L := ((algebraMap M L).comp (algebraMap K M)).toAlgebra
  let _ : IsScalarTower K M L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra ℚ L := ((algebraMap K L).comp (algebraMap ℚ K)).toAlgebra
  let _ : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower ℚ M L := IsScalarTower.to₁₃₄ ℚ K M L
  let _ : Module.Finite K L := Module.Finite.trans M L
  let _ : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K M L
  let φ := φ₂.comp φ₁
  have hφ (a : A) : (φ a : L) = algebraMap K L a := by
    change (φ₂ (φ₁ a) : L) = _
    rw [hφ₂, hφ₁]
    rfl
  have he : (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K) :=
    WeierstrassLocalCoefficientExtension.compatibility_of_apply φ hφ
  have hC' := WeierstrassLocalNodalTransport.normalized_changeEquation φ W he E C hC T
  have hD' := WeierstrassLocalCoefficientExtension.changeEquation φ he V U D hD
  let C' := T.map (algebraMap B L) * C.map (algebraMap K L)
  let r' := fun a ↦ WeierstrassLocalKernelCoverExtension.sectionMap
    E (W.map φ₁) (T • W.map φ) (C.map (algebraMap K M)) C' hC₁ hC' i (r a) (hr a)
  refine ⟨L, fieldL, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    B, dvrB, perfB, φ, T, depth, φ₂ π, hC', hD', m, r', inferInstance, hφ,
    FiniteExtensionValuationSubring.comap_eq A B (algebraMap K L) φ hφ, hT, ?_, ?_, ?_, ?_⟩
  · simpa only [map_map] using hd
  · intro a
    exact WeierstrassLocalKernelCoverExtension.sectionMap_structure
      E (W.map φ₁) (T • W.map φ) (C.map (algebraMap K M)) C' hC₁ hC' i (r a) (hr a)
  · intro a
    let _ := hi a
    exact WeierstrassLocalKernelCoverExtension.sectionMap_isOpenImmersion
      E (W.map φ₁) (T • W.map φ) (C.map (algebraMap K M)) C' hC₁ hC' i (r a) (hr a)
  · exact WeierstrassLocalKernelCoverExtension.sectionMap_covers
      E (W.map φ₁) (T • W.map φ) (C.map (algebraMap K M)) C' hC₁ hC' i r hr hc

end WeierstrassCurve.Velu
