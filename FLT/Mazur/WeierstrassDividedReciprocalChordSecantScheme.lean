/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordSecantSource

/-!
# Whole reciprocal chord/secant output comparison

An actual tangent localization lift on the overlap compares both formulas
on arbitrary schemes, including nonreduced ones.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "num" => dividedTangentNumerator W s b3 b4 b6 a c
local notation "den" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "dx" => a (x W s b3 b4 b6) - c (x W s b3 b4 b6)
local notation "dy" => a (y W s b3 b4 b6) - c (y W s b3 b4 b6)

local notation "Q" => DividedReciprocalChordRing W s b3 b4 b6 a c
local notation "C" => DividedReciprocalChordOutputRing W s b3 b4 b6 a c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedSecantRing W s b3 b4 b6 a c
local notation "jc" => (IsScalarTower.toAlgHom R Q C).comp (IsScalarTower.toAlgHom R S Q)
local notation "jv" => IsScalarTower.toAlgHom R S V
local notation "jt" => IsScalarTower.toAlgHom R S T
variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The two outputs coincide over every common algebra refinement of their localization sources. -/
theorem dividedReciprocalChordSecant_toCurve
    (e : C →ₐ[R] B) (f : V →ₐ[R] B) (h : e.comp jc = f.comp jv) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalChordToCurve W s b3 b4 b6 a c h3 h4 h6 =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  let v := dividedReciprocalChordSecantTangentLift W s b3 b4 b6 a c e f h
  have hv : v.comp jt = e.comp jc :=
    dividedReciprocalChordSecantTangentLift_source W s b3 b4 b6 a c e f h
  have hc := dividedReciprocalChordTangentOutput_toCurve W s b3 b4 b6 a c e v
    (by simpa only [AlgHom.comp_assoc] using hv.symm) h3 h4 h6
  have hs := dividedTangentSecant_scheme W s b3 b4 b6 a c h3 h4 h6
    (Spec.map (CommRingCat.ofHom v.toRingHom)) (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun z : S →ₐ[R] B => Spec.map (CommRingCat.ofHom z.toRingHom))
        (hv.trans h))
  exact hc.trans hs

/-- Whole outputs agree on every affine scheme over both genuine localization domains. -/
theorem dividedReciprocalChordSecant_affineScheme {B : Type u} [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of C)) (g : Spec (.of B) ⟶ Spec (.of V))
    (h : f ≫ Spec.map (CommRingCat.ofHom (jc).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap S V))) :
    f ≫ dividedReciprocalChordToCurve W s b3 b4 b6 a c h3 h4 h6 =
      g ≫ dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  let e₀ : C →+* B := (Spec.preimage f).hom
  let f₀ : V →+* B := (Spec.preimage g).hom
  have he : Spec.map (CommRingCat.ofHom e₀) = f := Spec.map_preimage f
  have hf : Spec.map (CommRingCat.ofHom f₀) = g := Spec.map_preimage g
  have heq : e₀.comp (jc).toRingHom = f₀.comp (algebraMap S V) := by
    rw [← he, ← hf, ← Spec.map_comp, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let _ : Algebra R B := (e₀.comp (algebraMap R C)).toAlgebra
  let e : C →ₐ[R] B := { e₀ with commutes' := fun _ => rfl }
  let v : V →ₐ[R] B := by
    refine { f₀ with commutes' := ?_ }
    intro r
    change f₀ (algebraMap R V r) = e₀ (algebraMap R C r)
    have hr := DFunLike.congr_fun heq (algebraMap R S r)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply R S V] using hr.symm
  have hb : e.comp jc = v.comp jv := by
    ext z
    exact DFunLike.congr_fun heq z
  have hout := dividedReciprocalChordSecant_toCurve W s b3 b4 b6 a c h3 h4 h6 e v hb
  change Spec.map (CommRingCat.ofHom e₀) ≫ _ =
    Spec.map (CommRingCat.ofHom f₀) ≫ _ at hout
  simpa only [he, hf] using hout

/-- The comparison holds on arbitrary common scheme refinements, preserving nilpotents. -/
theorem dividedReciprocalChordSecant_scheme {X : Scheme.{u}}
    (f : X ⟶ Spec (.of C)) (g : X ⟶ Spec (.of V))
    (h : f ≫ Spec.map (CommRingCat.ofHom (jc).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap S V))) :
    f ≫ dividedReciprocalChordToCurve W s b3 b4 b6 a c h3 h4 h6 =
      g ≫ dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  apply X.affineCover.hom_ext
  intro i
  let k := (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  apply (cancel_epi (X.affineCover.X i).isoSpec.inv).mp
  have hk : (k ≫ f) ≫ Spec.map (CommRingCat.ofHom (jc).toRingHom) =
      (k ≫ g) ≫ Spec.map (CommRingCat.ofHom (algebraMap S V)) := by
    simp only [Category.assoc, h]
  simpa only [k, Category.assoc] using
    dividedReciprocalChordSecant_affineScheme W s b3 b4 b6 a c h3 h4 h6 (k ≫ f) (k ≫ g) hk

end FLT.Mazur.WeierstrassDilatation
