/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalKernelSplitDepthModel
public import FLT.Mazur.WeierstrassOriginalResolvedKernel

/-!
# The constructed original prime kernel in the resolved smooth model

The constructed splitting field, DVR, tangent normalization and full cover
supply the resolution inputs. Its full kernel closure is closed in the relative
smooth open and has degree p over the whole DVR. Both original source and
quotient-target equations remain among the constructed data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.WeierstrassDividedDepth
namespace WeierstrassCurve.Velu
set_option backward.isDefEq.respectTransparency false
variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  {K : Type} [Field K] [Algebra ℚ K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  (V : WeierstrassCurve ℚ) (W U : WeierstrassCurve A) (C D : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap A K))
  (hD : D • V.map (algebraMap ℚ K) = U.map (algebraMap A K))
local notation "i" => primeKernelRationalMap E p q hq hfixed

include hC hD in
/-- Construct the full original kernel's closed smooth-locus embedding with retained degree p. -/
theorem primeLocalKernel_exists_resolved_model
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
      (hd : SplitNodeDepth (T • W.map φ) π depth)
      (m : ℕ) (r : Fin m → (Spec (.of L) ⟶ localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i))
      (hr : ∀ a, r a ≫ localGenericKernelInclusion E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i ≫
          integralCurveStructure ((T • W.map φ).map (algebraMap B L)) = 𝟙 _)
      (hc : ∀ x : localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i,
        ∃ a z, r a z = x),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧ T.u = 1 ∧ (∀ a, IsOpenImmersion (r a)) ∧
      IsClosedImmersion (WeierstrassOriginalResolvedKernel.inclusion B E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' hd i r hr hc) ∧
      FCurve.FiniteLocallyFreeDegree
        (finiteGlobalKernelClosureStructure hd.uniformizer_ne_zero (splitResolutionData B hd)
          (depth / 2) (le_refl _)
          (WeierstrassOriginalResolvedKernel.genericDiscriminant B E (T • W.map φ)
            (T.map (algebraMap B L) * C.map (algebraMap K L)) hC')
          (localGenericKernelInclusion E (T • W.map φ)
            (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' i)) p := by
  obtain ⟨L, field, algK, algQ, tower, fin, sep, B, dvr, perf, φ, T, depth, π,
      hC', hD', m, r, loc, hφ, hB, hT, hd, hr, hi, hc⟩ :=
    primeLocalKernel_exists_splitDepth_model E p q hq hfixed A V W U C D hC hD hΔ h4
  let _ := field
  let _ := algK
  let _ := algQ
  let _ := tower
  let _ := fin
  let _ := sep
  let _ := dvr
  let _ := perf
  refine ⟨L, field, algK, algQ, tower, fin, sep, B, dvr, perf, φ, T, depth, π,
    hC', hD', hd, m, r, hr, hc, loc, hφ, hB, hT, hi, inferInstance, ?_⟩
  have hdeg : FCurve.FiniteLocallyFreeDegree (i ≫ integralCurveStructure E) p := by
    rw [primeKernelRationalMap_base]
    exact primeKernelRationalScheme_degree E p q hq hfixed
  have h := WeierstrassOriginalResolvedKernel.inclusion_degree B E (T • W.map φ)
    (T.map (algebraMap B L) * C.map (algebraMap K L)) hC' hd i r hr hc p hdeg
  change FCurve.FiniteLocallyFreeDegree
    (resolvedKernelSmoothInclusion _ _ _ _ _ _ _ ≫ _ ≫ _) p at h
  rw [resolvedKernelSmoothInclusion_structure] at h
  exact h

end WeierstrassCurve.Velu
