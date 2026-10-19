/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalKernelResolvedModel
public import FLT.Mazur.PadicValuationArithmetic

/-!
# The original prime kernel over the arithmetic p-adic base

The residue field of the actual p-adic integer subring is finite, hence
perfect. This supplies the arithmetic input to the constructed split-depth
resolution without assuming perfectness of an arbitrary residue field.
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
  (ℓ : ℕ) [Fact ℓ.Prime]
  (V : WeierstrassCurve ℚ) (W U : WeierstrassCurve (padicIntegerSubring ℓ))
  (C D : VariableChange ℚ_[ℓ])
  (hC : C • E.map (algebraMap ℚ ℚ_[ℓ]) = W.map (algebraMap (padicIntegerSubring ℓ) ℚ_[ℓ]))
  (hD : D • V.map (algebraMap ℚ ℚ_[ℓ]) = U.map (algebraMap (padicIntegerSubring ℓ) ℚ_[ℓ]))
local notation "i" => primeKernelRationalMap E p q hq hfixed

include hC hD in
/-- The actual p-adic base supplies a resolved full original kernel of degree p. -/
theorem primePadicKernel_exists_resolved_model
    (hΔ : W.Δ ∈ maximalIdeal (padicIntegerSubring ℓ)) (h4 : IsUnit W.c₄) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[ℓ] L) (_ : Algebra ℚ L)
      (_ : IsScalarTower ℚ ℚ_[ℓ] L) (_ : Module.Finite ℚ_[ℓ] L)
      (_ : Algebra.IsSeparable ℚ_[ℓ] L)
      (B : ValuationSubring L) (_ : IsDiscreteValuationRing B)
      (_ : PerfectField (ResidueField B)) (φ : padicIntegerSubring ℓ →+* B)
      (T : VariableChange B) (depth : ℕ) (π : B)
      (hC' : (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) •
        E.map (algebraMap ℚ L) = (T • W.map φ).map (algebraMap B L))
      (_hD' : D.map (algebraMap ℚ_[ℓ] L) • V.map (algebraMap ℚ L) =
        (U.map φ).map (algebraMap B L))
      (hd : SplitNodeDepth (T • W.map φ) π depth)
      (m : ℕ) (r : Fin m → (Spec (.of L) ⟶ localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC' i))
      (hr : ∀ a, r a ≫ localGenericKernelInclusion E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC' i ≫
          integralCurveStructure ((T • W.map φ).map (algebraMap B L)) = 𝟙 _)
      (hc : ∀ x : localGenericKernel E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC' i,
        ∃ a z, r a z = x),
      IsLocalHom φ ∧ (∀ a : padicIntegerSubring ℓ, (φ a : L) = algebraMap ℚ_[ℓ] L a) ∧
      B.comap (algebraMap ℚ_[ℓ] L) = padicIntegerSubring ℓ ∧ T.u = 1 ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      IsClosedImmersion (WeierstrassOriginalResolvedKernel.inclusion B E (T • W.map φ)
        (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC' hd i r hr hc) ∧
      FCurve.FiniteLocallyFreeDegree
        (finiteGlobalKernelClosureStructure hd.uniformizer_ne_zero (splitResolutionData B hd)
          (depth / 2) (le_refl _)
          (WeierstrassOriginalResolvedKernel.genericDiscriminant B E (T • W.map φ)
            (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC')
          (localGenericKernelInclusion E (T • W.map φ)
            (T.map (algebraMap B L) * C.map (algebraMap ℚ_[ℓ] L)) hC' i)) p := by
  let _ : IsDiscreteValuationRing (padicIntegerSubring ℓ) :=
    padicIntegerSubring_isDiscreteValuationRing ℓ
  let _ : Finite (ResidueField (padicIntegerSubring ℓ)) :=
    padicIntegerSubring_residue_finite ℓ
  let _ : PerfectField (ResidueField (padicIntegerSubring ℓ)) := inferInstance
  exact primeLocalKernel_exists_resolved_model E p q hq hfixed
    (padicIntegerSubring ℓ) V W U C D hC hD hΔ h4

end WeierstrassCurve.Velu
