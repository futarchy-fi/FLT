/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXModificationLocalization
public import FLT.Mazur.WeierstrassSuccessiveXContraction
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# Incidence-open transport over the original Weierstrass cubic

The successive and product-scale modification charts have isomorphic
incidence opens. The comparison also preserves their full original cubic
contractions, before any residue specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" => WeierstrassModificationX.Coordinate W (s * π) b3 b4 b6
local notation "L" => XOpen W s π b3 b4 b6
local notation "M" => ModificationIncidenceOpen W s π b3 b4 b6

/-- The successive chart maps to the original product-scale modification chart. -/
def modificationMorphism : Spec (.of A) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (modificationMap W s π b3 b4 b6).toRingHom)

/-- The actual incidence-open comparison as an isomorphism of schemes. -/
def modificationIncidenceIso : Spec (.of L) ≅ Spec (.of M) :=
  Scheme.Spec.mapIso
    (modificationIncidenceEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The incidence-open isomorphism retains the complete original modification map. -/
@[reassoc] theorem modificationIncidenceIso_toModification :
    (modificationIncidenceIso W s π b3 b4 b6).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B M)) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫
        modificationMorphism W s π b3 b4 b6 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (modificationIncidenceForward_base W s π b3 b4 b6)

variable (h3 : W.a₃ = (s * π) * b3) (h4 : W.a₄ = (s * π) * b4)
  (h6 : W.a₆ = (s * π) ^ 2 * b6)
local notation "h3'" => h3.trans (mul_assoc s π b3)
local notation "h4'" => h4.trans (mul_assoc s π b4)
local notation "h6'" => h6.trans (by ring : (s * π) ^ 2 * b6 = s ^ 2 * (π ^ 2 * b6))

/-- Every original affine cubic function agrees through the successive comparison. -/
theorem modificationMap_fromOriginal :
    (modificationMap W s π b3 b4 b6).comp
        (WeierstrassModificationX.fromOriginal W (s * π) b3 b4 b6 h3 h4 h6) =
      (fromDivided W s π b3 b4 b6).comp
        (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6)
          h3' h4' h6') := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change modificationMap W s π b3 b4 b6
      (WeierstrassModificationX.fromOriginal W (s * π) b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0)) =
      fromDivided W s π b3 b4 b6
        (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6)
          h3' h4' h6' (WeierstrassIntegralChart.coord W 2 0))
    simp only [WeierstrassModificationX.fromOriginal_x, modificationMap_x,
      WeierstrassDilatation.fromOriginal_x, map_mul,
      AlgHom.commutes, fromDivided_x]
  · change modificationMap W s π b3 b4 b6
      (WeierstrassModificationX.fromOriginal W (s * π) b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1)) =
      fromDivided W s π b3 b4 b6
        (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6)
          h3' h4' h6' (WeierstrassIntegralChart.coord W 2 1))
    simp only [WeierstrassModificationX.fromOriginal_y, WeierstrassModificationX.y,
      map_mul, modificationMap_x, modificationMap_v,
      WeierstrassDilatation.fromOriginal_y, AlgHom.commutes, fromDivided_y, mul_assoc]
  · change ((modificationMap W s π b3 b4 b6).comp _)
      (WeierstrassIntegralChart.coord W 2 2) =
        ((fromDivided W s π b3 b4 b6).comp _) (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- The comparison preserves the same original projective cubic contraction. -/
@[reassoc] theorem modificationMorphism_toCurve :
    modificationMorphism W s π b3 b4 b6 ≫
        WeierstrassModificationX.toCurve W (s * π) b3 b4 b6 h3 h4 h6 =
      toCurve W s π b3 b4 b6 h3' h4' h6' := by
  have h := congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] A =>
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassIntegralChart.integralCurveChart W 2)
      (modificationMap_fromOriginal W s π b3 b4 b6 h3 h4 h6)
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, modificationMorphism, WeierstrassModificationX.toCurve,
    toCurve, toDivided, WeierstrassDilatation.toCurve] using h

end FLT.Mazur.WeierstrassSuccessiveX
