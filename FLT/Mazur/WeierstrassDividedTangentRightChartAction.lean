/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentReverseScheme
public import FLT.Mazur.WeierstrassDividedTangentReverseSecantScheme
public import FLT.Mazur.WeierstrassDividedTangentSchemeAction
public import FLT.Mazur.WeierstrassDividedSecantSchemeAction
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# Right smooth action on the reversed slope overlaps

Comparing over the complete common input ring retains both inputs. Each
reversed formula therefore gives the actual right smooth action on its overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "l" => Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom)
local notation "r" => Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom)
local notation "v" => toCurve W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- The tangent output equals the right smooth action on the reversed tangent overlap. -/
theorem dividedTangent_rightTangentAction {X : Scheme.{u}} (f : X ⟶ Spec (.of T))
    (g : X ⟶ Spec (.of (DividedTangentRing W s b3 b4 b6 c a)))
    (hg : g ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (DividedTangentRing W s b3 b4 b6 c a))) =
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (p : X ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ r ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ l ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ l ≫ v) hb := by
  let U := DividedTangentRing W s b3 b4 b6 c a
  let ju := IsScalarTower.toAlgHom R S U
  have hi (z : Coordinate W s b3 b4 b6 →ₐ[R] S) :
      g ≫ Spec.map (CommRingCat.ofHom (ju.comp z).toRingHom) =
        f ≫ Spec.map (CommRingCat.ofHom ((j).comp z).toRingHom) := by
    have h := congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom z.toRingHom)) hg
    simp only [Category.assoc, ← Spec.map_comp] at h
    convert h using 1 <;> congr 2
  have hl : g ≫ Spec.map (CommRingCat.ofHom (ju.comp c).toRingHom) ≫ v =
      p ≫ (integralSmoothOpen W).ι := by rw [← Category.assoc, hi, Category.assoc, hp]
  have hr : g ≫ Spec.map (CommRingCat.ofHom (ju.comp a).toRingHom) ≫ v =
      f ≫ l ≫ v := by rw [← Category.assoc, hi, Category.assoc]
  have hb' : p ≫ integralSmoothStructure W =
      (g ≫ Spec.map (CommRingCat.ofHom (ju.comp a).toRingHom) ≫ v) ≫
        integralCurveStructure W := by rw [hr]; exact hb
  have he := dividedTangent_schemeAction W s b3 b4 b6 c a h3 h4 h6 g p hl hb'
  dsimp only [ju, U] at hr
  simp only [hr] at he
  exact (dividedTangentReverse_scheme
    W s b3 b4 b6 a c h3 h4 h6 f g hg.symm).trans he

/-- The tangent output equals the right smooth action on the reversed secant overlap. -/
theorem dividedTangent_rightSecantAction {X : Scheme.{u}} (f : X ⟶ Spec (.of T))
    (g : X ⟶ Spec (.of (DividedSecantRing W s b3 b4 b6 c a)))
    (hg : g ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (DividedSecantRing W s b3 b4 b6 c a))) =
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (p : X ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ r ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ l ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ l ≫ v) hb := by
  let U := DividedSecantRing W s b3 b4 b6 c a
  let ju := IsScalarTower.toAlgHom R S U
  have hi (z : Coordinate W s b3 b4 b6 →ₐ[R] S) :
      g ≫ Spec.map (CommRingCat.ofHom (ju.comp z).toRingHom) =
        f ≫ Spec.map (CommRingCat.ofHom ((j).comp z).toRingHom) := by
    have h := congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom z.toRingHom)) hg
    simp only [Category.assoc, ← Spec.map_comp] at h
    convert h using 1 <;> congr 2
  have hl : g ≫ Spec.map (CommRingCat.ofHom (ju.comp c).toRingHom) ≫ v =
      p ≫ (integralSmoothOpen W).ι := by rw [← Category.assoc, hi, Category.assoc, hp]
  have hr : g ≫ Spec.map (CommRingCat.ofHom (ju.comp a).toRingHom) ≫ v =
      f ≫ l ≫ v := by rw [← Category.assoc, hi, Category.assoc]
  have hb' : p ≫ integralSmoothStructure W =
      (g ≫ Spec.map (CommRingCat.ofHom (ju.comp a).toRingHom) ≫ v) ≫
        integralCurveStructure W := by rw [hr]; exact hb
  have he := dividedSecant_schemeAction W s b3 b4 b6 c a h3 h4 h6 g p hl hb'
  dsimp only [ju, U] at hr
  simp only [hr] at he
  exact (dividedTangentReverseSecant_scheme
    W s b3 b4 b6 a c h3 h4 h6 f g hg.symm).trans he

end FLT.Mazur.WeierstrassDilatation
