/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreCyclicIso

/-! # Composition of coordinate and cyclic transports

Identified coordinate changes compose by multiplication of variable changes.
Transport on nonzero torsion and cyclic parameters preserves identity and
composition. The local Legendre changes satisfy the double-swap and reciprocal
inverse products. These results do not yet construct the permutation action
on the descended family: comparison on common coefficient covers remains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Identified affine coordinate maps compose by multiplying variable changes. -/
theorem variableChangeIdentifiedAffineMap_comp
    (W V U : WeierstrassCurve R) (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = U) :
    (variableChangeIdentifiedAffineMap V U C hC).comp
      (variableChangeIdentifiedAffineMap W V D hD) =
        variableChangeIdentifiedAffineMap W U (C * D) (by rw [mul_smul, hD, hC]) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeIdentifiedAffineMap V U C hC
    (variableChangeIdentifiedAffineMap W V D hD (coord W false i)) =
    variableChangeIdentifiedAffineMap W U (C * D) (by rw [mul_smul, hD, hC]) (coord W false i)
  fin_cases i <;> simp [variableChangeIdentifiedAffineMap_coord, VariableChange.mul_def] <;> ring

private theorem specAlgHom_comp {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] (f : B →ₐ[R] T) (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  Spec.map_comp (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom f.toRingHom)

private theorem square_comp {A B C D E F : Scheme.{u}}
    {i : A ⟶ B} {j : C ⟶ D} {k : E ⟶ F}
    {f : B ⟶ D} {g : D ⟶ F} {f' : A ⟶ C} {g' : C ⟶ E}
    (h₁ : i ≫ f = f' ≫ j) (h₂ : j ≫ g = g' ≫ k) :
    i ≫ (f ≫ g) = (f' ≫ g') ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

attribute [local irreducible] variableChangeCongrOverIso

/-- Composition of identified changes agrees with the product on the affine chart. -/
theorem variableChangeCongrOverIso_comp_chart
    (W V U : WeierstrassCurve R) (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = U) :
    affineChart U ≫ ((variableChangeCongrOverIso V U C hC).hom.left ≫
      (variableChangeCongrOverIso W V D hD).hom.left) =
        affineChart U ≫
          (variableChangeCongrOverIso W U (C * D) (by rw [mul_smul, hD, hC])).hom.left := by
  have hsq := square_comp (affineChart_variableChangeCongr V U C hC)
    (affineChart_variableChangeCongr W V D hD)
  rw [hsq, affineChart_variableChangeCongr]
  have hh := congrArg (fun f : Ring W false →ₐ[R] Ring U false =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
    (variableChangeIdentifiedAffineMap_comp W V U C D hD hC)
  rw [specAlgHom_comp] at hh
  exact congrArg (fun f => f ≫ affineChart W) hh

/-- The global identified coordinate isomorphisms compose by multiplication. -/
theorem variableChangeCongrOverIso_trans
    (W V U : WeierstrassCurve R) (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = U) :
    (variableChangeCongrOverIso V U C hC) ≪≫ (variableChangeCongrOverIso W V D hD) =
      variableChangeCongrOverIso W U (C * D) (by rw [mul_smul, hD, hC]) := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  change (variableChangeCongrOverIso V U C hC).hom.left ≫
    (variableChangeCongrOverIso W V D hD).hom.left = _
  apply affineChart_hom_ext U (toBase W)
  · rw [Category.assoc, variableChangeCongr_toBase, variableChangeCongr_toBase,
      variableChangeCongr_toBase]
  · exact variableChangeCongrOverIso_comp_chart W V U C D hD hC

variable [IsNoetherianRing R] [IsDomain R]
variable {V W U : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic] [U.IsElliptic]
local instance isoReflIsMonHom (W : WeierstrassCurve R) [W.IsElliptic] :
    IsMonHom (Iso.refl (groupModel W)).hom :=
  inferInstanceAs (IsMonHom (𝟙 (groupModel W)))

local instance isoTransIsMonHom
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.hom] [IsMonHom f.hom] : IsMonHom (e ≪≫ f).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ f.hom))

local instance isoTransInvIsMonHom
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.inv] [IsMonHom f.inv] : IsMonHom (e ≪≫ f).inv :=
  inferInstanceAs (IsMonHom (f.inv ≫ e.inv))

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
/-- The forward map of torsion transport is the transport of the forward map. -/
theorem torsionTransportIso_hom_map
    (e : groupModel V ≅ groupModel W) [IsMonHom e.hom] [IsMonHom e.inv] :
    (torsionTransportIso e n).hom = torsionTransport e.hom n := rfl

omit [NeZero n] in
/-- Forward torsion transport preserves composition of group isomorphisms. -/
theorem torsionTransportIso_hom_trans
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv] :
    (torsionTransportIso (e ≪≫ f) n).hom =
      (torsionTransportIso e n).hom ≫ (torsionTransportIso f n).hom :=
  by
    rw [torsionTransportIso_hom_map, torsionTransportIso_hom_map,
      torsionTransportIso_hom_map]
    exact (torsionTransport_congr (show (e ≪≫ f).hom = e.hom ≫ f.hom from rfl) n).trans
      (torsionTransport_comp e.hom f.hom n).symm

attribute [local irreducible] groupNonzeroTorsionTransportIso

/-- Transport by the identity fixes nonzero torsion. -/
theorem groupNonzeroTorsionTransportIso_refl (W : WeierstrassCurve R) [W.IsElliptic] :
    groupNonzeroTorsionTransportIso n (Iso.refl (groupModel W)) = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
  rw [groupNonzeroTorsionTransportIso_inclusion]
  change nonzeroTorsionInclusion W n ≫ torsionTransport (𝟙 (groupModel W)) n = _
  rw [torsionTransport_id]
  simp

/-- Nonzero torsion transport preserves composition. -/
theorem groupNonzeroTorsionTransportIso_trans
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv] :
    groupNonzeroTorsionTransportIso n (e ≪≫ f) =
      (groupNonzeroTorsionTransportIso n e) ≪≫ (groupNonzeroTorsionTransportIso n f) := by
  apply Iso.ext
  apply (cancel_mono (nonzeroTorsionInclusion U n)).mp
  rw [groupNonzeroTorsionTransportIso_inclusion, Iso.trans_hom, Category.assoc,
    groupNonzeroTorsionTransportIso_inclusion, ← Category.assoc,
    groupNonzeroTorsionTransportIso_inclusion, Category.assoc]
  rw [torsionTransportIso_hom_trans]

variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
omit [NeZero n] in
/-- Transport by the identity fixes cyclic parameters. -/
theorem groupCyclicParameterIso_refl (W : WeierstrassCurve R) [W.IsElliptic] :
    groupCyclicParameterIso p (Iso.refl (groupModel W)) = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap W p)).mp
  rw [← groupCyclicParameterIso_quotient, groupNonzeroTorsionTransportIso_refl]
  simp

omit [NeZero n] in
/-- Cyclic parameter transport preserves composition. -/
theorem groupCyclicParameterIso_trans
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv] :
    groupCyclicParameterIso p (e ≪≫ f) =
      (groupCyclicParameterIso p e) ≪≫ (groupCyclicParameterIso p f) := by
  apply Iso.ext
  apply (cancel_epi (scalarQuotientMap V p)).mp
  rw [← groupCyclicParameterIso_quotient, groupNonzeroTorsionTransportIso_trans,
    Iso.trans_hom, Category.assoc, groupCyclicParameterIso_quotient,
    ← Category.assoc, groupCyclicParameterIso_quotient]
  simp only [Iso.trans_hom, Category.assoc]

section LocalRelations
variable {A : Type u} [CommRing A]
/-- Two root swaps give the sign change on the Weierstrass coordinates. -/
theorem legendreSwapChange_mul_self (u : Aˣ) (hu : (u : A) ^ 2 = -1) :
    legendreSwapChange u * legendreSwapChange u = signCoordinateChange (-1) 0 := by
  ext <;> simp only [legendreSwapChange, signCoordinateChange, VariableChange.mul_def]
  all_goals simp [← pow_two, hu]

/-- Reciprocal scalings with inverse roots compose to the identity. -/
theorem legendreReciprocalChange_inv_mul (u : Aˣ) :
    legendreReciprocalChange u⁻¹ * legendreReciprocalChange u = 1 := by
  ext <;> simp [legendreReciprocalChange, VariableChange.mul_def, VariableChange.one_def]

end LocalRelations
end WeierstrassCurve.CubicCharts
