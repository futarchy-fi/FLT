/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalKernelSplitModel
public import FLT.Mazur.FiniteEtalePerfectDVRSplitting

/-!
# Perfect-residue splitting of the original local source kernel

Construct a perfect-residue DVR and a full rational kernel cover on the
extended original cubic. Perfectness of the new residue field is derived
from the original residue field; both original variable changes are retained.
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
  [PerfectField (IsLocalRing.ResidueField A)]
  (V : WeierstrassCurve ℚ) (W U : WeierstrassCurve A) (C D : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap A K))
  (hD : D • V.map (algebraMap ℚ K) = U.map (algebraMap A K))
local notation "i" => primeKernelRationalMap E p q hq hfixed

include hC hD in
/-- Construct the full source cover on the actual extended cubic, retaining both equations. -/
theorem primeLocalKernel_exists_perfect_split_model :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra ℚ L)
      (_ : IsScalarTower ℚ K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (B : ValuationSubring L) (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B)
      (_ : PerfectField (IsLocalRing.ResidueField B)) (φ : A →+* B)
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
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hf : IsFinite (i ≫ integralCurveStructure E) := by
    rw [primeKernelRationalMap_base]
    exact primeKernelRationalScheme_finite E p q hq hfixed
  have he : Etale (i ≫ integralCurveStructure E) := by
    rw [primeKernelRationalMap_base]
    exact primeKernelRationalScheme_etale E p q hq hfixed
  let _ := hf
  let _ := he
  let _ := WeierstrassLocalKernelCoefficientSquare.isFinite E W C hC i
  let _ := WeierstrassLocalKernelCoefficientSquare.etale E W C hC i
  obtain ⟨L, hL, aL, finL, sepL, B, hdvr, hnoeth, perf, φ,
      n, r, hlocal, hφ, hB, hr, hi, hc⟩ :=
    FiniteEtalePerfectDVRSplitting.exists_splitting A
      (localGenericKernelInclusion E W C hC i ≫
        integralCurveStructure (W.map (algebraMap A K)))
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
  refine ⟨L, hL, aL, inferInstance, inferInstance, finL, sepL, B, hdvr, hnoeth,
    perf, φ, hC', hD', n, r', hlocal, hφ, hB, ?_, ?_, ?_⟩
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
