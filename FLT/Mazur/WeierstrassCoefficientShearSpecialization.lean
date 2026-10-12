/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.NodeTangentCoefficientNaturality
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual coefficient specialization between complete equation gluings

Specialize the entire glued model along an original coefficient algebra map.
Both projections are retained; in particular the residue-root model maps into
the integral-root model by the actual tangent coefficient specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)
local notation "sS" => coefficientShearGluedStructure hπ data S r j hj
local notation "sT" => coefficientShearGluedStructure hπ data T v j hj
local notation "pS" => coefficientShearGluedProjection hπ data S r j hj
local notation "pT" => coefficientShearGluedProjection hπ data T v j hj
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "qT" => Spec.map (CommRingCat.ofHom (algebraMap R T))
local notation "b" => Spec.map (CommRingCat.ofHom f.toRingHom)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "E" => coefficientShearGluedIso hπ data S r j hj

/-- The original coefficient square commutes on every function. -/
theorem coefficientShearSpecialization_square : (sT ≫ b) ≫ qS = pT ≫ base := by
  have hf : b ≫ qS = qT := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)
  rw [Category.assoc, hf]
  exact (coefficientShearGlued_isPullback hπ data T v j hj).w

/-- The entire coefficient model specializes, without choosing a chart or a component. -/
def coefficientShearSpecialization :
    coefficientShearGlued hπ data T v j hj ⟶ coefficientShearGlued hπ data S r j hj :=
  pullback.lift (sT ≫ b) pT
    (coefficientShearSpecialization_square hπ data S T v j hj f) ≫ (E).inv

/-- The coefficient leg is the actual original specialization. -/
@[reassoc] theorem coefficientShearSpecialization_structure :
    coefficientShearSpecialization hπ data S T r v j hj f ≫ sS = sT ≫ b := by
  simp only [coefficientShearSpecialization, coefficientShearGluedStructure,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- Every original integral-model function is preserved by specialization. -/
@[reassoc] theorem coefficientShearSpecialization_projection :
    coefficientShearSpecialization hπ data S T r v j hj f ≫ pS = pT := by
  simp only [coefficientShearSpecialization, coefficientShearGluedProjection,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The two actual projections determine specialization on every source scheme. -/
theorem coefficientShearSpecialization_unique {Z : Scheme.{u}}
    (g : Z ⟶ coefficientShearGlued hπ data T v j hj)
    (h : Z ⟶ coefficientShearGlued hπ data S r j hj)
    (hs : h ≫ sS = g ≫ sT ≫ b) (hp : h ≫ pS = g ≫ pT) :
    h = g ≫ coefficientShearSpecialization hπ data S T r v j hj f := by
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · rw [Category.assoc, coefficientShearSpecialization_structure, hs]
  · rw [Category.assoc, coefficientShearSpecialization_projection, hp]

section Residue
variable [IsLocalRing R]
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))

/-- The original tangent residue map as an algebra map over the original integral ring. -/
def tangentResidueCoefficientAlgHom : A →ₐ[R] Q where
  __ := nodeTangentCoefficientMap W (residue R)
  commutes' x := by
    change nodeTangentCoefficientMap W (residue R) (algebraMap R A x) = algebraMap R Q x
    rw [nodeTangentCoefficientMap_coeff, IsScalarTower.algebraMap_apply R (ResidueField R) Q,
      ResidueField.algebraMap_eq]

/-- The actual whole residue-root equation gluing maps to the integral-root equation gluing. -/
def coefficientShearTangentSpecialization :=
  coefficientShearSpecialization hπ data A Q
    (AdjoinRoot.root (nodeTangentPolynomial W))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) j hj
    (tangentResidueCoefficientAlgHom (W := W))

end Residue
end FLT.Mazur.WeierstrassDividedDepth
