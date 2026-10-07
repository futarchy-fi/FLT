/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreCyclicRelations

/-! # Local cyclic relations and the descended return swap

Coordinate products equal to the identity or elliptic negation induce the
identity on cyclic parameters. This gives local double-swap and reciprocal
relations. On the universal Legendre base, the return swap descends over the
same quadratic cover and is inverse to the previously constructed swap in
both orders. Mixed permutation relations and comparison of different
coefficient covers remain separate obligations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]
attribute [local irreducible] variableChangeCongrOverIso

/-- The identity change fixes the affine coordinate ring. -/
theorem variableChangeIdentifiedAffineMap_one (W : WeierstrassCurve R) :
    variableChangeIdentifiedAffineMap W W 1 (one_smul _ _) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change variableChangeIdentifiedAffineMap W W 1 (one_smul _ _) (coord W false i) =
    coord W false i
  fin_cases i <;> simp [variableChangeIdentifiedAffineMap_coord, VariableChange.one_def]

/-- The identity change induces the identity curve isomorphism. -/
theorem variableChangeCongrOverIso_one (W : WeierstrassCurve R) :
    variableChangeCongrOverIso W W 1 (one_smul _ _) = Iso.refl _ := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply affineChart_hom_ext W (toBase W)
  · change _ = 𝟙 (scheme W) ≫ toBase W
    rw [variableChangeCongr_toBase, Category.id_comp]
  · rw [affineChart_variableChangeCongr, variableChangeIdentifiedAffineMap_one]
    simp

variable [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
local instance : IsMonHom (Iso.refl (groupModel W)).hom :=
  inferInstanceAs (IsMonHom (𝟙 (groupModel W)))

/-- Equal group isomorphisms give equal cyclic transports. -/
theorem groupCyclicParameterIso_congr {V : WeierstrassCurve R} [V.IsElliptic]
    (e f : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
    (h : e = f) :
    groupCyclicParameterIso p e = groupCyclicParameterIso p f := by
  subst f
  rfl

/-- The identity coordinate change fixes cyclic parameters. -/
theorem variableChangeCyclic_one :
    groupCyclicParameterIso p (variableChangeCongrOverIso W W 1 (one_smul _ _)) =
      Iso.refl _ := by
  exact (groupCyclicParameterIso_congr W p _ _ (variableChangeCongrOverIso_one W)).trans
    (groupCyclicParameterIso_refl p W)

/-- Elliptic negation fixes cyclic parameters. -/
theorem signCoordinateCyclic_neg_one (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hneg : signCoordinateChange (-1) 0 • W = W) :
    groupCyclicParameterIso p
      (variableChangeCongrOverIso W W (signCoordinateChange (-1) 0) hneg) =
        Iso.refl _ := by
  have hpos : signCoordinateChange (1 : Rˣ) 0 • W = W := one_smul _ _
  have h := groupCyclicParameterIso_neg p
    (variableChangeCongrOverIso W W (signCoordinateChange 1 0) hpos)
    (variableChangeCongrOverIso W W (signCoordinateChange (-1) 0) hneg)
    (signCoordinateChange_over W W ha₁ ha₃ 1 0 hpos hneg)
  exact h.symm.trans (variableChangeCyclic_one W p)

local instance cyclicTransHom {V U : WeierstrassCurve R} [V.IsElliptic] [U.IsElliptic]
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.hom] [IsMonHom f.hom] : IsMonHom (e ≪≫ f).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ f.hom))
local instance cyclicTransInv {V U : WeierstrassCurve R} [V.IsElliptic] [U.IsElliptic]
    (e : groupModel V ≅ groupModel W) (f : groupModel W ≅ groupModel U)
    [IsMonHom e.inv] [IsMonHom f.inv] : IsMonHom (e ≪≫ f).inv :=
  inferInstanceAs (IsMonHom (f.inv ≫ e.inv))

/-- Cyclic coordinate transport respects multiplication of changes. -/
theorem variableChangeCyclic_trans (V U : WeierstrassCurve R)
    [V.IsElliptic] [U.IsElliptic] (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = U) :
    groupCyclicParameterIso p (variableChangeCongrOverIso V U C hC) ≪≫
      groupCyclicParameterIso p (variableChangeCongrOverIso W V D hD) =
        groupCyclicParameterIso p
          (variableChangeCongrOverIso W U (C * D) (by rw [mul_smul, hD, hC])) := by
  exact (groupCyclicParameterIso_trans p _ _).symm.trans
    (groupCyclicParameterIso_congr W p _ _ (variableChangeCongrOverIso_trans W V U C D hD hC))

/-- Equal coordinate changes induce equal cyclic transports. -/
theorem variableChangeCyclic_congr (V : WeierstrassCurve R) [V.IsElliptic]
    (C D : VariableChange R) (hC : C • W = V) (hD : D • W = V) (h : C = D) :
    groupCyclicParameterIso p (variableChangeCongrOverIso W V C hC) =
      groupCyclicParameterIso p (variableChangeCongrOverIso W V D hD) := by
  subst D
  rfl

/-- An identity coordinate product induces identity cyclic transport. -/
theorem variableChangeCyclic_trans_of_product_one
    (V : WeierstrassCurve R) [V.IsElliptic] (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = W) (hmul : C * D = 1) :
    groupCyclicParameterIso p (variableChangeCongrOverIso V W C hC) ≪≫
      groupCyclicParameterIso p (variableChangeCongrOverIso W V D hD) = Iso.refl _ := by
  exact (variableChangeCyclic_trans W p V W C D hD hC).trans
    ((variableChangeCyclic_congr W p W _ 1 _ (one_smul _ _) hmul).trans
      (variableChangeCyclic_one W p))

/-- A negation coordinate product induces identity cyclic transport. -/
theorem variableChangeCyclic_trans_of_product_neg
    (V : WeierstrassCurve R) [V.IsElliptic] (C D : VariableChange R)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hD : D • W = V) (hC : C • V = W)
    (hmul : C * D = signCoordinateChange (-1) 0) :
    groupCyclicParameterIso p (variableChangeCongrOverIso V W C hC) ≪≫
      groupCyclicParameterIso p (variableChangeCongrOverIso W V D hD) = Iso.refl _ := by
  have hneg : signCoordinateChange (-1 : Rˣ) 0 • W = W := by
    rw [← hmul, mul_smul, hD, hC]
  exact (variableChangeCyclic_trans W p V W C D hD hC).trans
    ((variableChangeCyclic_congr W p W _ _ _ hneg hmul).trans
      (signCoordinateCyclic_neg_one W p ha₁ ha₃ hneg))

omit [W.IsElliptic] in
/-- Two local swaps induce the identity on cyclic parameters. -/
theorem legendreSwapCyclic_double (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1)
    [(legendreCurve l).IsElliptic] [(legendreCurve (1 - l)).IsElliptic] :
    groupCyclicParameterIso p
        (variableChangeCongrOverIso (legendreCurve (1 - l)) (legendreCurve l)
          (legendreSwapChange u) (by simpa using legendreSwapChange_curve (1 - l) u hu)) ≪≫
      legendreSwapCyclicParameterIso p l u hu = Iso.refl _ := by
  exact variableChangeCyclic_trans_of_product_neg (legendreCurve l) p
    (legendreCurve (1 - l)) _ _ rfl rfl (legendreSwapChange_curve l u hu)
    (by simpa using legendreSwapChange_curve (1 - l) u hu) (legendreSwapChange_mul_self u hu)

omit [W.IsElliptic] in
/-- Reciprocal transport with the inverse root returns cyclic parameters. -/
theorem legendreReciprocalCyclic_double (l u : Rˣ) (hu : (u : R) ^ 2 = l)
    [(legendreCurve (l : R)).IsElliptic]
    [(legendreCurve ((l⁻¹ : Rˣ) : R)).IsElliptic] :
    groupCyclicParameterIso p
        (variableChangeCongrOverIso (legendreCurve ((l⁻¹ : Rˣ) : R)) (legendreCurve (l : R))
          (legendreReciprocalChange u⁻¹) (by
            have hi : ((u⁻¹ : Rˣ) : R) ^ 2 = (l⁻¹ : Rˣ) := by
              have h : u ^ 2 = l := Units.ext hu
              change ((u⁻¹ ^ 2 : Rˣ) : R) = ((l⁻¹ : Rˣ) : R)
              rw [inv_pow, h]
            simpa using legendreReciprocalChange_curve l⁻¹ u⁻¹ hi)) ≪≫
      legendreReciprocalCyclicParameterIso p l u hu = Iso.refl _ := by
  apply variableChangeCyclic_trans_of_product_one
  exact legendreReciprocalChange_inv_mul u

section Descent
variable (V : WeierstrassCurve R) [V.IsElliptic]
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]

/-- A local product equal to negation descends to the identity. -/
theorem quadraticCoordinateDesc_comp_of_product_neg
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (hv₁ : V.a₁ = 0) (hv₃ : V.a₃ = 0)
    (r s : R)
    (hD : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d)))
    (hC : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) s) •
      V.map (algebraMap R (QuadraticEtaleRing d)) = W.map (algebraMap R (QuadraticEtaleRing d)))
    (hmul : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) s) *
      signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) =
        signCoordinateChange (-1) 0) :
    quadraticCoordinateDesc V p d W hv₁ hv₃ s hC ≫
      quadraticCoordinateDesc W p d V ha₁ ha₃ r hD = 𝟙 _ := by
  have hw₁ : (W.map (algebraMap R (QuadraticEtaleRing d))).a₁ = 0 := by
    change algebraMap R _ W.a₁ = 0
    rw [ha₁, map_zero]
  have hw₃ : (W.map (algebraMap R (QuadraticEtaleRing d))).a₃ = 0 := by
    change algebraMap R _ W.a₃ = 0
    rw [ha₃, map_zero]
  have hlocal := variableChangeCyclic_trans_of_product_neg
    (W.map (algebraMap R (QuadraticEtaleRing d))) p
    (V.map (algebraMap R (QuadraticEtaleRing d))) _ _ hw₁ hw₃ hD hC hmul
  have hh := congrArg (fun e => e.hom.left) hlocal
  simp only [Iso.trans_hom, Over.comp_left, Iso.refl_hom, Over.id_left] at hh
  apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)).mp
  rw [← Category.assoc, quadraticCoordinateDesc_fac, Category.assoc,
    quadraticCoordinateDesc_fac, ← Category.assoc, hh]
  simp
end Descent

/-- The same quadratic root sends the swapped Legendre equation back. -/
theorem legendreSwap_return_coordinate_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
      (algebraMap (LegendreBase p) (LegendreSwapRing (LegendreBase p)) 1) •
      (legendreCurve (1 - legendreParameter p)).map
        (algebraMap (LegendreBase p) (LegendreSwapRing (LegendreBase p))) =
      (legendreModel p).map
        (algebraMap (LegendreBase p) (LegendreSwapRing (LegendreBase p))) := by
  simpa only [map_one, legendreCurve_map, map_sub, legendreModel, sub_sub_cancel,
    signCoordinateChange, legendreSwapChange]
    using legendreSwapChange_curve
      (1 - algebraMap (LegendreBase p) (LegendreSwapRing (LegendreBase p)) (legendreParameter p))
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) (legendreSwapRoot_square p)

/-- The return swap descended to the universal coefficient base. -/
def legendreSwapReturnDescendedMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreModel p) p).left ⟶
      (scalarQuotientModel (legendreCurve (1 - legendreParameter p)) p).left :=
  quadraticCoordinateDesc (legendreCurve (1 - legendreParameter p)) p
    (-1 : (LegendreBase p)ˣ) (legendreModel p) rfl rfl 1
    (legendreSwap_return_coordinate_equation p)

/-- The descended return followed by the original swap is the identity. -/
theorem legendreSwapReturnDescendedMap_comp (p : ℕ) [Fact p.Prime] :
    legendreSwapReturnDescendedMap p ≫ legendreSwapDescendedMap p = 𝟙 _ := by
  apply quadraticCoordinateDesc_comp_of_product_neg
  simpa only [map_one, signCoordinateChange, legendreSwapChange]
    using legendreSwapChange_mul_self
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) (legendreSwapRoot_square p)

/-- The original swap followed by the descended return is the identity. -/
theorem legendreSwapDescendedMap_comp_return (p : ℕ) [Fact p.Prime] :
    legendreSwapDescendedMap p ≫ legendreSwapReturnDescendedMap p = 𝟙 _ := by
  let : IsIso (legendreSwapDescendedMap p) :=
    quadraticCoordinateDescIsIso (legendreModel p)
      (legendreCurve (1 - legendreParameter p)) p (-1 : (LegendreBase p)ˣ)
      rfl rfl 1 (legendreSwap_coordinate_equation p)
  apply (cancel_mono (legendreSwapDescendedMap p)).mp
  rw [Category.assoc, legendreSwapReturnDescendedMap_comp,
    Category.comp_id, Category.id_comp]

end WeierstrassCurve.CubicCharts
