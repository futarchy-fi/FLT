/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalIntegralKernelRecovery
public import FLT.Mazur.WeierstrassDividedKernelContraction

/-!
# The original prime kernel in each concrete divided integral model

Apply the divided closure construction to the original nonconstant source
kernel of the actual local quotient. Its full degree p, original generic
inclusion and finite surjective comparison with the retained cubic closure
are proved without a singular-locus avoidance hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.WeierstrassDividedDepth

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Retain the same enumeration of the original geometric kernel. -/
local instance dividedKernelFiniteFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (dividedKernelFiniteFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

variable [IsDomain R] [ValuationRing R] [IsFractionRing R L]
  {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (k : Fin (n + 1)) → Data W π (start + k.val)) (j : ℕ) (hj : j ≤ n)

local notation "hΔ" => (primeLocalSource_isElliptic E W C hC).isUnit

include hp hcurve hD in
/-- The full divided closure of the original prime source kernel is finite flat. -/
theorem primeLocalDividedKernelClosure_finite_flat :
    IsFinite (finiteGlobalKernelClosureStructure hπ data j hj hΔ iL) ∧
      Flat (finiteGlobalKernelClosureStructure hπ data j hj hΔ iL) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsFinite (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.1
  let _ : Flat (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.2.1
  exact ⟨finiteGlobalKernelClosureStructure_finite hπ data j hj hΔ iL,
    finiteGlobalKernelClosureStructure_flat hπ data j hj hΔ iL⟩

include hp hcurve hD in
/-- The actual divided closure retains degree p over the original Noetherian valuation base. -/
theorem primeLocalDividedKernelClosure_degree [IsNoetherianRing R] :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (finiteGlobalKernelClosureStructure hπ data j hj hΔ iL) p :=
  finiteGlobalKernelClosureStructure_degree hπ data j hj hΔ iL p
    (primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD)

include hp hcurve hD in
/-- Its comparison with the exact original full cubic closure is finite and surjective. -/
theorem primeLocalDividedKernelClosure_contraction_finite_surjective :
    IsFinite (finiteGlobalKernelClosureContraction hπ data j hj hΔ iL) ∧
      Surjective (finiteGlobalKernelClosureContraction hπ data j hj hΔ iL) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsFinite (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.1
  let _ : Flat (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.2.1
  exact ⟨finiteGlobalKernelClosureContraction_finite hπ data j hj hΔ iL, inferInstance⟩

omit [Fintype (torsionKernel E p q)] in
/-- The full original nonconstant prime kernel is exactly the divided closure's generic fiber. -/
theorem primeLocalDividedKernelClosure_isPullback :
    IsPullback (finiteGlobalKernelToClosure hπ data j hj hΔ iL) iL
      (finiteGlobalKernelClosureInclusion hπ data j hj hΔ iL)
      (finiteGlobalGenericCurve hπ data j hj hΔ) :=
  finiteGlobalKernelClosureInclusion_isPullback hπ data j hj hΔ iL

end WeierstrassCurve.Velu
