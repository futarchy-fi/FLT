/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalIntegralKernelRecovery
public import FLT.Mazur.WeierstrassValuationKernelClosureDegree

/-!
# The original prime kernel has its actual finite flat integral closure

Use the proved generic degree p, generic-fiber recovery and valuation finiteness
on the exact original kernel inclusion. This retains the rational target and
local variable change, including when the residue characteristic is p.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Retain the same enumeration of the original geometric kernel. -/
local instance integralKernelFiniteFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralKernelFiniteFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

include hp hcurve hD in
/-- The same original schematic closure is finite flat over the original valuation base. -/
theorem primeLocalIntegralKernelClosure_finite_flat [IsDomain R] [ValuationRing R]
    [IsFractionRing R L] :
    IsFinite (genericKernelClosureStructure W iL) ∧ Flat (genericKernelClosureStructure W iL) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsFinite (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.1
  let _ : Flat (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := hd.2.1
  exact genericKernelClosureStructure_finite_flat W iL

include hp hcurve hD in
/-- Construct the finite flat original closed model with its exact recovered generic fiber. -/
theorem exists_primeLocalIntegralFiniteFlatKernel [IsDomain R] [ValuationRing R]
    [IsFractionRing R L] :
    ∃ (H : Scheme) (j : H ⟶ integralCurve W)
      (a : localGenericKernel E W C hC i ⟶ H),
      IsClosedImmersion j ∧ IsFinite (j ≫ integralCurveStructure W) ∧
      Flat (j ≫ integralCurveStructure W) ∧ IsSchemeTheoreticallyDominant a ∧
      IsPullback a iL j (integralCoefficientMorphism W) := by
  obtain ⟨hf, hflat⟩ :=
    primeLocalIntegralKernelClosure_finite_flat E p q hp V hcurve hfixed hq W U C D hC hD
  exact ⟨genericKernelClosure W iL, genericKernelClosureInclusion W iL,
    genericKernelToClosure W iL, inferInstance, hf, hflat, inferInstance,
    genericKernelClosureInclusion_isPullback W iL⟩

include hp hcurve hD in
/-- Over a Noetherian valuation base, the original integral kernel has full degree p. -/
theorem primeLocalIntegralKernelClosure_degree [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [IsFractionRing R L] :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree (genericKernelClosureStructure W iL) p :=
  genericKernelClosureStructure_degree W iL p
    (primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD)

end WeierstrassCurve.Velu
