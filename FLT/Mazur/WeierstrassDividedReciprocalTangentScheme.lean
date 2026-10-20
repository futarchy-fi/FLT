/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalTangentComparison

/-!
# Scheme-valued reciprocal/tangent compatibility

Agreement over the full divided pair source identifies the original outputs
on every scheme refinement, including nonreduced overlaps.
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
local notation "T" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W s b3 b4 b6 a c
local notation "Q" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "jt" => (IsScalarTower.toAlgHom R Q T).comp (IsScalarTower.toAlgHom R S Q)
local notation "it" => Spec.map (CommRingCat.ofHom (jt).toRingHom)
local notation "iv" => Spec.map (CommRingCat.ofHom (algebraMap S V))

/-- The two original formulas agree on every affine refinement of their actual overlap. -/
theorem dividedReciprocalTangent_affineScheme {B : Type u} [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of T)) (g : Spec (.of B) ⟶ Spec (.of V))
    (h : f ≫ it = g ≫ iv) :
    f ≫ dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      g ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  let e₀ : T →+* B := (Spec.preimage f).hom
  let f₀ : V →+* B := (Spec.preimage g).hom
  have he : Spec.map (CommRingCat.ofHom e₀) = f := Spec.map_preimage f
  have hf : Spec.map (CommRingCat.ofHom f₀) = g := Spec.map_preimage g
  have heq : e₀.comp (jt).toRingHom = f₀.comp (algebraMap S V) := by
    rw [← he, ← hf, ← Spec.map_comp, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let _ : Algebra R B := (e₀.comp (algebraMap R T)).toAlgebra
  let e : T →ₐ[R] B := { e₀ with commutes' := fun _ => rfl }
  let v : V →ₐ[R] B := by
    refine { f₀ with commutes' := ?_ }
    intro r
    change f₀ (algebraMap R V r) = e₀ (algebraMap R T r)
    have hr := DFunLike.congr_fun heq (algebraMap R S r)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply R S V] using hr.symm
  have hb : (e.comp (IsScalarTower.toAlgHom R Q T)).comp (IsScalarTower.toAlgHom R S Q) =
      v.comp (IsScalarTower.toAlgHom R S V) := by
    ext z
    exact DFunLike.congr_fun heq z
  have hout := dividedReciprocalTangentOutput_toCurve W s b3 b4 b6 a c e v hb h3 h4 h6
  change Spec.map (CommRingCat.ofHom e₀) ≫ _ =
    Spec.map (CommRingCat.ofHom f₀) ≫ _ at hout
  simpa only [he, hf] using hout



/-- The actual original outputs coincide on arbitrary scheme refinements of the two opens. -/
theorem dividedReciprocalTangent_scheme {X : Scheme.{u}}
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V)) (h : f ≫ it = g ≫ iv) :
    f ≫ dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      g ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  apply X.affineCover.hom_ext
  intro i
  let k := (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  apply (cancel_epi (X.affineCover.X i).isoSpec.inv).mp
  have hk : (k ≫ f) ≫ it = (k ≫ g) ≫ iv := by simp only [Category.assoc, h]
  simpa only [k, Category.assoc] using
    dividedReciprocalTangent_affineScheme W s b3 b4 b6 a c h3 h4 h6 (k ≫ f) (k ≫ g) hk

end FLT.Mazur.WeierstrassDilatation
