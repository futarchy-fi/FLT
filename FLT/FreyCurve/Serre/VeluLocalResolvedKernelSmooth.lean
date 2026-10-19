/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalIntegralKernelRecovery
public import FLT.Mazur.WeierstrassResolvedKernelSmoothEmbedding

/-!
# The original prime source kernel in the resolved relative smooth model

A finite rational cover of the exact original generic source kernel places
its full degree-p closure inside the split resolution's own smooth locus.
The rational target and original variable changes are retained in the degree
proof. Constructing the required arithmetic splitting extension remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur
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
local instance resolvedKernelSmoothFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (resolvedKernelSmoothFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L : Type} [Field L] [Algebra ℚ L]
  (A : ValuationSubring L) [IsNoetherianRing A]
  (W U : WeierstrassCurve A) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap A L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap A L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

variable {π : A} {depth : ℕ} (N : SplitNodeDepth W π depth)
  {J : Type} [Finite J]
  (r : J → (Spec (.of L) ⟶
    localGenericKernel E W C hC (primeKernelRationalMap E p q hq hfixed)))
  (hr : ∀ a, r a ≫
    localGenericKernelInclusion E W C hC (primeKernelRationalMap E p q hq hfixed) ≫
      integralCurveStructure (W.map (algebraMap A L)) = 𝟙 _)
  (hcover : ∀ x : localGenericKernel E W C hC (primeKernelRationalMap E p q hq hfixed),
    ∃ a z, r a z = x)
local notation "hΔ" => (primeLocalSource_isElliptic E W C hC).isUnit
local notation "data" => splitResolutionData A N
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero N
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)

include hr hcover in
omit [Fintype (torsionKernel E p q)] in
/-- Every point of the full original prime closure lies in the resolved relative smooth open. -/
theorem primeLocalResolvedKernelClosure_range_smooth :
    Set.range (finiteGlobalKernelClosureInclusion hπ data (depth / 2) (le_refl _) hΔ iL) ⊆
      (f).smoothLocus :=
  resolvedKernelClosure_range_smooth A N hΔ iL r hr hcover

omit [Fintype (torsionKernel E p q)] in
/-- This is a closed embedding of the full original closure, not only its old smooth part. -/
theorem primeLocalResolvedKernelSmooth_closed :
    IsClosedImmersion (resolvedKernelSmoothInclusion A N hΔ iL r hr hcover) := inferInstance

include hp hcurve hD in
/-- The embedded full source kernel retains degree p from the actual original local quotient. -/
theorem primeLocalResolvedKernelSmooth_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (resolvedKernelSmoothInclusion A N hΔ iL r hr hcover ≫ (f).smoothLocus.ι ≫ f) p :=
  resolvedKernelSmoothInclusion_degree A N hΔ iL r hr hcover p
    (primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD)

end WeierstrassCurve.Velu
