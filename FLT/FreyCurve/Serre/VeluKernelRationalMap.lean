/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelAffineChart
public import FLT.Mazur.WeierstrassIntegralZeroSection
public import Mathlib.RingTheory.Idempotents

/-!
# The rational source-kernel map to the original cubic

The identity idempotent splits the rational spectrum into its affine and infinity
parts. The affine coordinate map and the zero section give an actual scheme map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The complementary quotient is the infinity part of the original rational algebra. -/
abbrev PrimeKernelInfinityAlgebra :=
  PrimeKernelDescentAlgebra E p q hq hfixed ⧸
    Ideal.span {1 - primeKernelIdentity E p q hq hfixed}

/-- The rational algebra splits using its original identity idempotent. -/
def primeKernelSplitEquiv : PrimeKernelDescentAlgebra E p q hq hfixed ≃ₐ[ℚ]
    PrimeKernelAffineAlgebra E p q hq hfixed × PrimeKernelInfinityAlgebra E p q hq hfixed :=
  AlgEquiv.prodQuotientOfIsIdempotentElem ℚ
    (primeKernelIdentity_idempotent E p q hq hfixed)
    (primeKernelIdentity_idempotent E p q hq hfixed).one_sub
    (by abel) (by
      rw [mul_sub, mul_one, (primeKernelIdentity_idempotent E p q hq hfixed).eq, sub_self])

/-- The affine and infinity spectra are exactly the original rational kernel spectrum. -/
def primeKernelSplitIso :
    Spec (.of (PrimeKernelAffineAlgebra E p q hq hfixed)) ⨿
      Spec (.of (PrimeKernelInfinityAlgebra E p q hq hfixed)) ≅
        Spec (.of (PrimeKernelDescentAlgebra E p q hq hfixed)) :=
  asIso (coprodSpec _ _) ≪≫
    Scheme.Spec.mapIso (primeKernelSplitEquiv E p q hq hfixed).toRingEquiv.toCommRingCatIso.op

/-- The affine summand is included by the actual idempotent quotient. -/
@[reassoc] theorem primeKernelSplitIso_inl :
    coprod.inl ≫ (primeKernelSplitIso E p q hq hfixed).hom =
      Spec.map (CommRingCat.ofHom (primeKernelAffineQuotient E p q hq hfixed).toRingHom) := by
  simp only [primeKernelSplitIso, Iso.trans_hom, asIso_hom, coprodSpec_inl_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The infinity summand is included by the complementary idempotent quotient. -/
@[reassoc] theorem primeKernelSplitIso_inr :
    coprod.inr ≫ (primeKernelSplitIso E p q hq hfixed).hom =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {1 - primeKernelIdentity E p q hq hfixed}))) := by
  simp only [primeKernelSplitIso, Iso.trans_hom, asIso_hom, coprodSpec_inr_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The map to the original rational cubic, assembled from its actual two parts. -/
def primeKernelRationalMap : Spec (.of (PrimeKernelDescentAlgebra E p q hq hfixed)) ⟶
    integralCurve E :=
  (primeKernelSplitIso E p q hq hfixed).inv ≫ coprod.desc
    (Spec.map (CommRingCat.ofHom (primeKernelAffineChart E p q hq hfixed).toRingHom) ≫
      integralCurveChart E 2)
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (PrimeKernelInfinityAlgebra E p q hq hfixed))) ≫
      integralCurveZero E)

/-- On the affine summand, the map is the original descended coordinate map. -/
@[reassoc] theorem primeKernelRationalMap_affine :
    Spec.map (CommRingCat.ofHom (primeKernelAffineQuotient E p q hq hfixed).toRingHom) ≫
      primeKernelRationalMap E p q hq hfixed =
        Spec.map (CommRingCat.ofHom (primeKernelAffineChart E p q hq hfixed).toRingHom) ≫
          integralCurveChart E 2 := by
  rw [← primeKernelSplitIso_inl, primeKernelRationalMap, Category.assoc,
    Iso.hom_inv_id_assoc, coprod.inl_desc]

/-- On the infinity summand, the map is the actual zero section. -/
@[reassoc] theorem primeKernelRationalMap_infinity :
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {1 - primeKernelIdentity E p q hq hfixed}))) ≫
      primeKernelRationalMap E p q hq hfixed =
        Spec.map (CommRingCat.ofHom
          (algebraMap ℚ (PrimeKernelInfinityAlgebra E p q hq hfixed))) ≫ integralCurveZero E := by
  rw [← primeKernelSplitIso_inr, primeKernelRationalMap, Category.assoc,
    Iso.hom_inv_id_assoc, coprod.inr_desc]

/-- The constructed map is defined over the original rational base. -/
@[reassoc] theorem primeKernelRationalMap_base :
    primeKernelRationalMap E p q hq hfixed ≫ integralCurveStructure E =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (PrimeKernelDescentAlgebra E p q hq hfixed))) := by
  apply (cancel_epi (primeKernelSplitIso E p q hq hfixed).hom).mp
  rw [primeKernelRationalMap, Category.assoc, Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc_assoc, Category.assoc, integralCurveChart_structure,
      primeKernelSplitIso_inl_assoc, chartStructure]
    rw [specAlgHom_structure, specAlgHom_structure]
  · simp only [coprod.inr_desc_assoc, Category.assoc, integralCurveZero_structure,
      Category.comp_id, primeKernelSplitIso_inr_assoc]
    rw [← Spec.map_comp]
    rfl

end WeierstrassCurve.Velu
