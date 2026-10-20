/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearTangentOutput
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction

/-!
# Scheme-valued tangent compatibility under integral shear

The original cubic outputs agree on every scheme refining the original and
sheared tangent opens over their common input source. Affine-cover descent
preserves the equality without imposing geometric-point or reducedness tests.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra R S] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing V s b3 (b4 - r * b3) b6 a' c'

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h3' : (rootShearCurve W r).a₃ = s * b3)
  (h4' : (rootShearCurve W r).a₄ = s * (b4 - r * b3))
  (h6' : (rootShearCurve W r).a₆ = s ^ 2 * b6)
local notation "C" => (WeierstrassCurve.VariableChange.mk 1 0 r 0)
local notation "hv" => (show C • W = V by unfold rootShearCurve; rfl)

local notation "E" => WeierstrassIntegralChart.integralVariableChangeIso W V C hv
local notation "it" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "it'" => Spec.map (CommRingCat.ofHom (algebraMap S T'))

/-- The sheared and original cubic maps agree on every affine common refinement. -/
theorem dividedShearTangent_affineScheme {B : Type} [CommRing B]
    (p : Spec (.of B) ⟶ Spec (.of T')) (q : Spec (.of B) ⟶ Spec (.of T))
    (hpq : p ≫ it' = q ≫ it) :
    p ≫ dividedTangentToCurve V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6' ≫ (E).hom =
      q ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
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
  have hout := dividedShearTangent_output W s b3 b4 b6 r a c e f hb
    h3 h4 h6 h3' h4' h6'
  rw [← he, ← hf]
  simp only [dividedTangentToCurve, Category.assoc,
    WeierstrassIntegralChart.integralVariableChangeIso_affine]
  simp only [← Category.assoc, ← Spec.map_comp]
  apply congrArg (· ≫ WeierstrassIntegralChart.integralCurveChart W 2)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom hout

/-- Both actual tangent outputs agree on arbitrary common scheme refinements. -/
theorem dividedShearTangent_scheme {X : Scheme}
    (p : X ⟶ Spec (.of T')) (q : X ⟶ Spec (.of T)) (hpq : p ≫ it' = q ≫ it) :
    p ≫ dividedTangentToCurve V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6' ≫ (E).hom =
      q ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  apply X.affineCover.hom_ext
  intro i
  let k := (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  apply (cancel_epi (X.affineCover.X i).isoSpec.inv).mp
  have hk : (k ≫ p) ≫ it' = (k ≫ q) ≫ it := by simp only [Category.assoc, hpq]
  simpa only [k, Category.assoc] using dividedShearTangent_affineScheme
    W s b3 b4 b6 r a c h3 h4 h6 h3' h4' h6' (k ≫ p) (k ≫ q) hk

end FLT.Mazur.WeierstrassDilatation
