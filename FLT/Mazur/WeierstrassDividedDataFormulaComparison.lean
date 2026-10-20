/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCrossDepthTangentScheme
public import FLT.Mazur.WeierstrassDividedCrossDepthTangentSecantScheme
public import FLT.Mazur.WeierstrassDividedCrossDepthSecantScheme
public import FLT.Mazur.WeierstrassDividedDepthStructure
public import FLT.Mazur.WeierstrassDividedTangentFlatSourceExt
public import FLT.Mazur.WeierstrassDividedReindexedSecantFlatSourceExt

/-!
# Compare divided formulas at independent depths

The actual original cubic inputs determine all four pairs of tangent/secant
formulas on a flat refinement. No original smooth-locus hypothesis is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [IsDomain R] [Module.Flat R S']
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (d' : Data W π l)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (a' c' : Coordinate W (π ^ l) d'.b3 d'.b4 d'.b6 →ₐ[R] S')

section
include hπ
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "V" => DividedTangentRing W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "e'" => IsScalarTower.toAlgHom R S' V

/-- Matching original inputs compare tangent and tangent formulas at any depths. -/
theorem dividedDataTangentTangent_compare {X : Scheme}
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V)) [Flat g]
    (ha : f ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : f ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d') :
    f ≫ dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 =
      g ≫ dividedTangentToCurve W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
        d'.factor3 d'.factor4 d'.factor6 := by
  let b := g ≫ Spec.map (CommRingCat.ofHom (algebraMap R V))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R V))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (g ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = b := by
    simpa only [Category.assoc, WeierstrassDividedDepth.toCurve_structure,
      specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) ha
  have h := dividedCrossDepthTangent_scheme
    W (π ^ k) d.b3 d.b4 d.b6 (π ^ l) d'.b3 d'.b4 d'.b6
    a c a' c' d.factor3 d.factor4 d.factor6 d'.factor3 d'.factor4 d'.factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) f g hb rfl
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using ha)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hc)
  exact h
end

section
include hπ
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "e'" => IsScalarTower.toAlgHom R S' V

/-- Matching original inputs compare tangent and secant formulas at any depths. -/
theorem dividedDataTangentSecant_compare {X : Scheme}
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V)) [Flat g]
    (ha : f ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : f ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d') :
    f ≫ dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 =
      g ≫ dividedSecantToCurve W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
        d'.factor3 d'.factor4 d'.factor6 := by
  let b := g ≫ Spec.map (CommRingCat.ofHom (algebraMap R V))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R V))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (g ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = b := by
    simpa only [Category.assoc, WeierstrassDividedDepth.toCurve_structure,
      specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) ha
  have h := dividedCrossDepthTangentSecant_scheme
    W (π ^ k) d.b3 d.b4 d.b6 (π ^ l) d'.b3 d'.b4 d'.b6
    a c a' c' d.factor3 d.factor4 d.factor6 d'.factor3 d'.factor4 d'.factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) f g hb rfl
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using ha)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hc)
  exact h
end

section
include hπ
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "V" => DividedTangentRing W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "e'" => IsScalarTower.toAlgHom R S' V

/-- Matching original inputs compare secant and tangent formulas at any depths. -/
theorem dividedDataSecantTangent_compare {X : Scheme}
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V)) [Flat g]
    (ha : f ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : f ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d') :
    f ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 =
      g ≫ dividedTangentToCurve W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
        d'.factor3 d'.factor4 d'.factor6 := by
  let b := g ≫ Spec.map (CommRingCat.ofHom (algebraMap R V))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R V))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (g ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = b := by
    simpa only [Category.assoc, WeierstrassDividedDepth.toCurve_structure,
      specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) ha
  have h := dividedCrossDepthTangentSecant_scheme
    W (π ^ l) d'.b3 d'.b4 d'.b6 (π ^ k) d.b3 d.b4 d.b6
    a' c' a c d'.factor3 d'.factor4 d'.factor6 d.factor3 d.factor4 d.factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) g f rfl hb
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using ha.symm)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hc.symm)
  exact h.symm
end

section
include hπ
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "e'" => IsScalarTower.toAlgHom R S' V

/-- Matching original inputs compare secant and secant formulas at any depths. -/
theorem dividedDataSecantSecant_compare {X : Scheme}
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V)) [Flat g]
    (ha : f ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : f ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫ toCurve d =
      g ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d') :
    f ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 =
      g ≫ dividedSecantToCurve W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
        d'.factor3 d'.factor4 d'.factor6 := by
  let b := g ≫ Spec.map (CommRingCat.ofHom (algebraMap R V))
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R V))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := inferInstanceAs (Flat (g ≫ _))
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = b := by
    simpa only [Category.assoc, WeierstrassDividedDepth.toCurve_structure,
      specAlgHom_structure] using
      congrArg (· ≫ integralCurveStructure W) ha
  have h := dividedCrossDepthSecant_scheme
    W (π ^ k) d.b3 d.b4 d.b6 (π ^ l) d'.b3 d'.b4 d'.b6
    a c a' c' d.factor3 d.factor4 d.factor6 d'.factor3 d'.factor4 d'.factor6
    b (IsRegular.of_ne_zero (pow_ne_zero _ hπ)) f g hb rfl
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using ha)
    (by simpa only [toCurve, WeierstrassDilatation.toCurve,
          AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
          Spec.map_comp, Category.assoc] using hc)
  exact h
end

end FLT.Mazur.WeierstrassDividedDepth
