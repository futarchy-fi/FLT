/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeTangentSecantOutput
public import FLT.Mazur.WeierstrassGlobalNegation

/-!
# Negative tangent and original secant compatibility on arbitrary schemes

Negating the negative-input tangent output agrees with the original
secant on every common scheme refinement. This compares the complete
morphisms, including over nonreduced sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra R S] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W s b3 b4 b6 a
local notation "c'" => branchNegativeInput W s b3 b4 b6 c
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing W s b3 b4 b6 a' c'

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "it" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "it'" => Spec.map (CommRingCat.ofHom (algebraMap S T'))

/-- The negative and original cubic maps agree on every affine common refinement. -/
theorem dividedNegativeTangentSecant_affineScheme {B : Type} [CommRing B]
    (p : Spec (.of B) ⟶ Spec (.of T')) (q : Spec (.of B) ⟶ Spec (.of T))
    (hpq : p ≫ it' = q ≫ it) :
    p ≫ dividedTangentToCurve W s b3 b4 b6 a' c' h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W =
      q ≫ dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  let e₀ : T' →+* B := (Spec.preimage p).hom
  let f₀ : T →+* B := (Spec.preimage q).hom
  have he : Spec.map (CommRingCat.ofHom e₀) = p := Spec.map_preimage p
  have hf : Spec.map (CommRingCat.ofHom f₀) = q := Spec.map_preimage q
  have heq : e₀.comp (algebraMap S T') = f₀.comp (algebraMap S T) := by
    rw [← he, ← hf, ← Spec.map_comp, ← Spec.map_comp] at hpq
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hpq)
  let _ : Algebra R B := (e₀.comp (algebraMap R T')).toAlgebra
  let e : T' →ₐ[R] B := { e₀ with commutes' := fun _ => rfl }
  let f : T →ₐ[R] B := by
    refine { f₀ with commutes' := ?_ }
    intro z
    change f₀ (algebraMap R T z) = e₀ (algebraMap R T' z)
    rw [IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R S T']
    exact (DFunLike.congr_fun heq (algebraMap R S z)).symm
  have hb : e.comp (IsScalarTower.toAlgHom R S T') =
      f.comp (IsScalarTower.toAlgHom R S T) := by
    ext z
    exact DFunLike.congr_fun heq z
  have hout := dividedNegativeTangentSecant_output W s b3 b4 b6 a c e f hb h3 h4 h6
  rw [← he, ← hf]
  simp only [dividedTangentToCurve, dividedSecantToCurve, Category.assoc,
    WeierstrassIntegralChart.integralCurveChart_negation_affine]
  simp only [← Category.assoc, ← Spec.map_comp]
  apply congrArg (· ≫ WeierstrassIntegralChart.integralCurveChart W 2)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom hout

/-- The negated tangent and original secant agree on arbitrary common scheme refinements. -/
theorem dividedNegativeTangentSecant_scheme {X : Scheme}
    (p : X ⟶ Spec (.of T')) (q : X ⟶ Spec (.of T)) (hpq : p ≫ it' = q ≫ it) :
    p ≫ dividedTangentToCurve W s b3 b4 b6 a' c' h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W =
      q ≫ dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  apply X.affineCover.hom_ext
  intro i
  let k := (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  apply (cancel_epi (X.affineCover.X i).isoSpec.inv).mp
  have hk : (k ≫ p) ≫ it' = (k ≫ q) ≫ it := by simp only [Category.assoc, hpq]
  simpa only [k, Category.assoc] using dividedNegativeTangentSecant_affineScheme
    W s b3 b4 b6 a c h3 h4 h6 (k ≫ p) (k ≫ q) hk

end FLT.Mazur.WeierstrassDilatation
