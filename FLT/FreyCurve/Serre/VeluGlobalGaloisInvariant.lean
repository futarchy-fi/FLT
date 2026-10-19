/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoefficientGaloisAction
public import FLT.FreyCurve.Serre.VeluGlobalBaseTarget
public import FLT.Mazur.AlgClosedSectionHomExt

/-!
# Galois invariance of the actual global Vélu morphism

The classical compatibility of the original coordinates now gives equality
of whole scheme morphisms to the exact original base target. Reducedness
and the dense closed points justify passing from sections to scheme maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero L] [IsAlgClosed L] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup (E.map (algebraMap K L)).toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K)
  (hV : V.map (algebraMap K L) = curve (E.map (algebraMap K L)) G)

local notation "EL" => E.map (algebraMap K L)

/-- The actual morphism to the original target is invariant under coefficient Galois action. -/
theorem veluGlobalToBaseTarget_galois
    (hG : ∀ (g : L ≃ₐ[K] L) P, P ∈ G →
      Affine.Point.map (W' := E.toAffine) g.toAlgHom P ∈ G)
    (g : L ≃ₐ[K] L) :
    integralGaloisMap E g ≫ veluGlobalToBaseTarget E G hodd V hV =
      veluGlobalToBaseTarget E G hodd V hV := by
  have h (P : (EL).toAffine.Point) (hP : P ∉ G) :
      (V.map (algebraMap K L)).toAffine.Nonsingular (xMap EL G P) (yMap EL G P) := by
    rw [hV]
    exact nonsingular_xMap_yMap_of_not_mem EL G hodd P hP
  apply FLT.Mazur.AlgClosedSectionHomExt.hom_ext
    (integralCurveStructure EL) (integralCurveStructure V)
  · rw [Category.assoc, veluGlobalToBaseTarget_base, integralGaloisMap_structure_assoc,
      galoisSpec_coefficient]
  · intro p hp
    obtain ⟨P, rfl⟩ := exists_affineSmoothPoint_of_section EL p hp
    let Q := Affine.Point.map (W' := E.toAffine) g.symm.toAlgHom P
    have hQ : Affine.Point.map (W' := E.toAffine) g.toAlgHom Q = P := by
      cases P <;> simp only [Q, Affine.Point.map, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]; rfl
    rw [← hQ, ← Category.assoc, integralGaloisMap_point E g Q, Category.assoc]
    exact (veluGlobalToBaseTarget_galois_points E G hodd V hV h hG g Q).symm

end WeierstrassCurve.Velu
