/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelMorphismComparison
public import FLT.GroupScheme.FaithfullyFlatMonoDescent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The rational source kernel is a closed subscheme of the original cubic

Monicity descends through the proved Cartesian square over Qbar. The rational
finite source is proper, so its monomorphism into the cubic is a closed immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The actual rational kernel scheme is finite over the original rational field. -/
instance primeKernelRationalScheme_finite :
    IsFinite (primeKernelRationalScheme E p q hq hfixed).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℚ _)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The original geometric closed inclusion detects monicity of the rational map. -/
instance primeKernelRationalMap_mono : Mono (primeKernelRationalMap E p q hq hfixed) := by
  have hb := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hcurve := (integralCoefficient_isPullback (S := AlgebraicClosure ℚ) E).flip
  let _ : Flat (integralCoefficientMorphism (S := AlgebraicClosure ℚ) E) :=
    MorphismProperty.of_isPullback hcurve hb.1
  let _ : Surjective (integralCoefficientMorphism (S := AlgebraicClosure ℚ) E) :=
    MorphismProperty.of_isPullback hcurve hb.2
  exact FLT.GroupScheme.mono_of_faithfullyFlat_pullback
    (primeKernelRationalMap_isPullback E p q hq hfixed)

/-- The rational map from the actual finite source is proper. -/
instance primeKernelRationalMap_proper : IsProper (primeKernelRationalMap E p q hq hfixed) := by
  have h : IsProper (primeKernelRationalMap E p q hq hfixed ≫ integralCurveStructure E) := by
    rw [primeKernelRationalMap_base]
    exact inferInstanceAs (IsProper (primeKernelRationalScheme E p q hq hfixed).hom)
  exact IsProper.of_comp _ (integralCurveStructure E)

/-- The constructed rational map embeds the actual descended kernel as a closed subscheme. -/
instance primeKernelRationalMap_closed :
    IsClosedImmersion (primeKernelRationalMap E p q hq hfixed) :=
  (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end WeierstrassCurve.Velu
