/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalKernelFiniteSplitting
public import FLT.Mazur.WeierstrassLocalCoefficientExtension
public import FLT.Mazur.WeierstrassLocalKernelTower

/-!
# Full rational kernel cover on the extended original local cubic

Construct a finite extension and a DVR, transport both original source and
quotient-target equations, and place the full rational section cover on the
source model's own local generic kernel. Neither model is replaced by a
rational subgroup, and no section or coefficient equation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart
namespace WeierstrassCurve.Velu
set_option backward.isDefEq.respectTransparency false
variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  {K : Type} [Field K] [Algebra ℚ K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A]
  (V : WeierstrassCurve ℚ) (W U : WeierstrassCurve A) (C D : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap A K))
  (hD : D • V.map (algebraMap ℚ K) = U.map (algebraMap A K))
local notation "i" => primeKernelRationalMap E p q hq hfixed

include hC hD in
/-- Construct the full source cover on the actual extended cubic, retaining both equations. -/
theorem primeLocalKernel_exists_split_model :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra ℚ L)
      (_ : IsScalarTower ℚ K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (B : ValuationSubring L) (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B)
      (φ : A →+* B)
      (hC' : C.map (algebraMap K L) • E.map (algebraMap ℚ L) =
        (W.map φ).map (algebraMap B L))
      (_hD' : D.map (algebraMap K L) • V.map (algebraMap ℚ L) =
        (U.map φ).map (algebraMap B L))
      (n : ℕ) (r : Fin n → (Spec (.of L) ⟶
        localGenericKernel E (W.map φ) (C.map (algebraMap K L)) hC' i)),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧
      (∀ a, r a ≫ localGenericKernelInclusion E (W.map φ)
        (C.map (algebraMap K L)) hC' i ≫
          integralCurveStructure ((W.map φ).map (algebraMap B L)) = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      (∀ x : localGenericKernel E (W.map φ) (C.map (algebraMap K L)) hC' i,
        ∃ a z, r a z = x) := by
  obtain ⟨L, hL, aL, finL, sepL, B, hdvr, hnoeth, φ, n, r, hlocal, hφ, hB, hr, hi, hc⟩ :=
    primeLocalKernel_exists_finite_splitting E p q hq hfixed A W C hC
  let _ := hL
  let _ := aL
  let _ := finL
  let _ := sepL
  let _ := hdvr
  let _ := hnoeth
  let _ : Algebra ℚ L := ((algebraMap K L).comp (algebraMap ℚ K)).toAlgebra
  let _ : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have he : (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K) :=
    WeierstrassLocalCoefficientExtension.compatibility_of_apply φ hφ
  have hC' := WeierstrassLocalCoefficientExtension.changeEquation φ he E W C hC
  have hD' := WeierstrassLocalCoefficientExtension.changeEquation φ he V U D hD
  let r' := fun a ↦ WeierstrassLocalKernelTower.sectionMap
    E W (W.map φ) C (C.map (algebraMap K L)) hC hC' i (r a)
  refine ⟨L, hL, aL, inferInstance, inferInstance, finL, sepL, B, hdvr, hnoeth, φ,
    hC', hD', n, r', hlocal, hφ, hB, ?_, ?_, ?_⟩
  · intro a
    exact (WeierstrassLocalKernelTower.sectionMap_structure
      E W (W.map φ) C (C.map (algebraMap K L)) hC hC' i (r a)).trans (hr a)
  · intro a
    let _ := hi a
    exact WeierstrassLocalKernelTower.sectionMap_isOpenImmersion
      E W (W.map φ) C (C.map (algebraMap K L)) hC hC' i (r a)
  · exact WeierstrassLocalKernelTower.sectionMap_covers
      E W (W.map φ) C (C.map (algebraMap K L)) hC hC' i r hc

end WeierstrassCurve.Velu
