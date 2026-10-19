/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalDegree
public import FLT.Mazur.WeierstrassLocalKernelCoefficientSquare
public import FLT.Mazur.FiniteEtaleDVRSplitting

/-!
# Finite splitting and an extended DVR for the original local prime source kernel

Construct the field, valuation ring and full rational section cover from the
original rational kernel inclusion and the specified local source coordinates.
The quotient target is not replaced by its rational subgroup.
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
  (W : WeierstrassCurve A) (C : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap A K))
local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "f" => localGenericKernelInclusion E W C hC i ≫
  integralCurveStructure (W.map (algebraMap A K))

/-- The entire original source kernel splits over a constructed finite extension with a DVR. -/
theorem primeLocalKernel_exists_finite_splitting :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L) (B : ValuationSubring L)
      (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B) (φ : A →+* B)
      (n : ℕ) (r : Fin n → (Spec (.of L) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧
      (∀ a, r a ≫ pullback.snd f _ = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      (∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme),
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
  exact FiniteEtaleDVRSplitting.exists_splitting A f

end WeierstrassCurve.Velu
