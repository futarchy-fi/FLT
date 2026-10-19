/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluPrimeRationalDegree
public import FLT.FreyCurve.Serre.VeluRationalKernelCover
public import FLT.Mazur.CommonCartesianCoverIso

/-!
# The original rational closed kernel is the actual identity fiber

The actual geometric kernel square descends through the original coefficient
covers. The resulting Cartesian square retains the previously constructed
rational closed inclusion and the exact rational Vélu target equation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Cache the same original finite subgroup on the mapped source cubic. -/
local instance primeRationalFiberFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeRationalFiberFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

variable (hq : Function.Surjective q)

local notation "φ" => primeRationalMorphism E p q hp V hcurve hfixed
local notation "H" => primeKernelClosedSubgroup E p q hq
local notation "D" => primeKernelRationalScheme E p q hq hfixed
local notation "a" => primeRationalKernelCover E p q hq hfixed
local notation "k" => Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))

/-- The original rational closed inclusion is killed by the actual rational morphism. -/
@[reassoc] theorem primeRationalMorphism_kernel_zero :
    primeKernelRationalMap E p q hq hfixed ≫ φ = (D).hom ≫ integralCurveZero V := by
  apply (cancel_epi a).mp
  rw [primeRationalKernelCover_inclusion_assoc, primeRationalMorphism_fac,
    primeGlobalToRationalTarget_factor, ← Category.assoc,
    (primeGlobalToExactTarget_kernel E p q hq hp V hcurve).w, Category.assoc,
    integralCoefficientMorphism_zero, primeRationalKernelCover_base_assoc]

/-- The original rational kernel maps canonically to the full actual identity fiber. -/
def primeRationalKernelToFiber : (D).left ⟶ pullback φ (integralCurveZero V) :=
  pullback.lift (primeKernelRationalMap E p q hq hfixed) (D).hom
    (primeRationalMorphism_kernel_zero E p q hp V hcurve hfixed hq)

/-- The fiber comparison retains exactly the original rational inclusion. -/
@[reassoc] theorem primeRationalKernelToFiber_fst :
    primeRationalKernelToFiber E p q hp V hcurve hfixed hq ≫ pullback.fst _ _ =
      primeKernelRationalMap E p q hq hfixed := pullback.lift_fst ..

/-- The fiber comparison retains the original rational kernel's structure map. -/
@[reassoc] theorem primeRationalKernelToFiber_snd :
    primeRationalKernelToFiber E p q hp V hcurve hfixed hq ≫ pullback.snd _ _ =
      (D).hom := pullback.lift_snd ..

/-- The entire original geometric kernel also recovers the full rational identity fiber. -/
theorem primeRationalKernelToFiber_isPullback :
    IsPullback (a ≫ primeRationalKernelToFiber E p q hp V hcurve hfixed hq)
      (H).carrier.hom (pullback.snd φ (integralCurveZero V)) k := by
  have B := ((primeGlobalToExactTarget_kernel E p q hq hp V hcurve).flip.paste_vert
    (primeRationalMorphism_isPullback E p q hp V hcurve hfixed).flip).flip
  have B' : IsPullback (H).carrier.hom
      ((a ≫ primeRationalKernelToFiber E p q hp V hcurve hfixed hq) ≫ pullback.fst _ _)
      (k ≫ integralCurveZero V) φ := by
    simpa only [Category.assoc, primeRationalKernelToFiber_fst,
      primeRationalKernelCover_inclusion, integralCoefficientMorphism_zero] using B.flip
  apply (B'.of_bot ?_ (IsPullback.of_hasPullback φ (integralCurveZero V)).flip).flip
  rw [Category.assoc, primeRationalKernelToFiber_snd, primeRationalKernelCover_base]

/-- The full identity fiber is the original rational kernel, including its scheme structure. -/
instance primeRationalKernelToFiber_isIso :
    IsIso (primeRationalKernelToFiber E p q hp V hcurve hfixed hq) := by
  have hk := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ := hk.1
  let _ := hk.2
  exact FLT.Mazur.CommonCartesianCoverIso.isIso
    (primeRationalKernelCover_isPullback E p q hq hfixed)
    (primeRationalKernelToFiber_isPullback E p q hp V hcurve hfixed hq)
    (primeRationalKernelToFiber E p q hp V hcurve hfixed hq) rfl
    (primeRationalKernelToFiber_snd E p q hp V hcurve hfixed hq)

/-- The original rational closed inclusion is exactly the Cartesian identity fiber. -/
theorem primeRationalMorphism_kernel :
    IsPullback (primeKernelRationalMap E p q hq hfixed) (D).hom φ (integralCurveZero V) :=
  IsPullback.of_iso_pullback
    ⟨primeRationalMorphism_kernel_zero E p q hp V hcurve hfixed hq⟩
    (asIso (primeRationalKernelToFiber E p q hp V hcurve hfixed hq))
    (primeRationalKernelToFiber_fst E p q hp V hcurve hfixed hq)
    (primeRationalKernelToFiber_snd E p q hp V hcurve hfixed hq)

end WeierstrassCurve.Velu
