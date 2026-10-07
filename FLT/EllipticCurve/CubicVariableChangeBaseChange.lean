/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreSign
public import FLT.EllipticCurve.CubicCyclicSign
public import FLT.EllipticCurve.CubicBaseChangeCyclic
/-! # Coordinate transport under coefficient extension

Admissible coordinate changes commute with coefficient extension on affine
coordinates and on the glued cubic schemes. Restriction to torsion,
removal of the zero section, and descent along the scalar quotient preserve
this compatibility. The final theorem concerns the actual cyclic transport
of an identified coordinate change, with its coefficient square proved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
variable (W V : WeierstrassCurve R) (C : VariableChange R) (h : C • W = V)
include h in
/-- Coefficient extension preserves an identified coordinate change. -/
theorem variableChange_map_equation :
    C.map (algebraMap R S) • W.map (algebraMap R S) = V.map (algebraMap R S) := by
  rw [map_variableChange, h]
/-- The affine coordinate pullbacks commute with coefficient extension. -/
theorem variableChangeAffine_coefficient :
    (chartCoefficientMap V S false).comp (variableChangeIdentifiedAffineMap W V C h).toRingHom =
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map (algebraMap R S)) (variableChange_map_equation S W V C h)).toRingHom.comp
          (chartCoefficientMap W S false) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change chartCoefficientMap V S false
      (variableChangeIdentifiedAffineMap W V C h (algebraMap R (Ring W false) r)) =
        variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
          (C.map (algebraMap R S)) (variableChange_map_equation S W V C h)
          (chartCoefficientMap W S false (algebraMap R (Ring W false) r))
    rw [AlgHom.commutes, chartCoefficientMap_scalar, chartCoefficientMap_scalar, AlgHom.commutes]
  · intro i
    change chartCoefficientMap V S false
      (variableChangeIdentifiedAffineMap W V C h (coord W false i)) =
        variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
          (C.map (algebraMap R S)) (variableChange_map_equation S W V C h)
          (chartCoefficientMap W S false (coord W false i))
    rw [variableChangeIdentifiedAffineMap_coord, chartCoefficientMap_coord,
      variableChangeIdentifiedAffineMap_coord]
    fin_cases i <;> simp [VariableChange.map, chartCoefficientMap_scalar]
/-- An identified coordinate change preserves the structure map. -/
theorem variableChangeCongr_toBase :
    (variableChangeCongrOverIso W V C h).hom.left ≫ toBase W = toBase V :=
  (variableChangeCongrOverIso W V C h).hom.w
attribute [local irreducible] variableChangeCongrOverIso
/-- The global coordinate change commutes with coefficient extension. -/
theorem variableChange_coefficient :
    (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
      (C.map (algebraMap R S)) (variableChange_map_equation S W V C h)).hom.left ≫
        coefficientMorphism W S =
      coefficientMorphism V S ≫ (variableChangeCongrOverIso W V C h).hom.left := by
  apply affineChart_hom_ext (V.map (algebraMap R S)) (toBase W)
  · simp only [Category.assoc, variableChangeCongr_toBase, coefficientMorphism_toBase]
    rw [← Category.assoc, variableChangeCongr_toBase]
  · simp only [← Category.assoc, affineChart_variableChangeCongr,
      affineChart_coefficientMorphism]
    simp only [Category.assoc]
    rw [affineChart_coefficientMorphism, affineChart_variableChangeCongr]
    simp only [← Category.assoc]
    change (Spec.map (CommRingCat.ofHom (variableChangeIdentifiedAffineMap
          (W.map (algebraMap R S)) (V.map (algebraMap R S))
          (C.map (algebraMap R S)) (variableChange_map_equation S W V C h)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap W S false))) ≫ affineChart W =
        (Spec.map (CommRingCat.ofHom (chartCoefficientMap V S false)) ≫
          Spec.map (CommRingCat.ofHom (variableChangeIdentifiedAffineMap W V C h).toRingHom)) ≫
            affineChart W
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (variableChangeAffine_coefficient S W V C h).symm

variable [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
variable [W.IsElliptic] [V.IsElliptic]

/-- The coefficient map on torsion agrees with the curve map after inclusion. -/
theorem coefficientTorsionMorphism_inclusion (n : ℕ) :
    coefficientTorsionMorphism W S n ≫ (torsionInclusion W n).left =
      (torsionInclusion (W.map (algebraMap R S)) n).left ≫ coefficientMorphism W S := by
  have ht := congrArg Over.Hom.left (coefficientTorsionIso_inclusion W S n)
  change _ ≫ _ = _ ≫ _ at ht
  dsimp only [coefficientTorsionMorphism]
  rw [Category.assoc, ← coefficientPullback_map_fst, ← Category.assoc, ht, Category.assoc]
  change (torsionInclusion (W.map (algebraMap R S)) n).left ≫
    (baseChangeIso W S).hom ≫ CategoryTheory.Limits.pullback.fst (toBase W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) = _
  rw [baseChangeIso_hom_fst]

/-- Restriction to torsion preserves a commuting coefficient square. -/
theorem torsionTransport_coefficient (n : ℕ)
    (f : groupModel V ⟶ groupModel W) [IsMonHom f]
    (g : groupModel (V.map (algebraMap R S)) ⟶ groupModel (W.map (algebraMap R S)))
    [IsMonHom g]
    (hg : g.left ≫ coefficientMorphism W S = coefficientMorphism V S ≫ f.left) :
    (torsionTransport g n).left ≫ coefficientTorsionMorphism W S n =
      coefficientTorsionMorphism V S n ≫ (torsionTransport f n).left := by
  apply (cancel_mono (torsionInclusion W n).left).mp
  have hf := congrArg Over.Hom.left (torsionTransport_inclusion f n)
  have hgg := congrArg Over.Hom.left (torsionTransport_inclusion g n)
  change _ ≫ _ = _ ≫ _ at hf hgg
  rw [Category.assoc, coefficientTorsionMorphism_inclusion, ← Category.assoc, hgg,
    Category.assoc, hg, ← Category.assoc, ← coefficientTorsionMorphism_inclusion,
    Category.assoc, ← hf, ← Category.assoc]


variable (e : groupModel V ≅ groupModel W) [IsMonHom e.hom] [IsMonHom e.inv]
variable (f : groupModel (V.map (algebraMap R S)) ≅ groupModel (W.map (algebraMap R S)))
variable [IsMonHom f.hom] [IsMonHom f.inv]
variable (hf : f.hom.left ≫ coefficientMorphism W S = coefficientMorphism V S ≫ e.hom.left)

include hf in
/-- Removing zero preserves compatibility of group transports with coefficients. -/
theorem groupNonzeroTransport_coefficient (n : ℕ) [NeZero n] :
    (groupNonzeroTorsionTransportIso n f).hom.left ≫ coefficientNonzeroTorsionMorphism W S n =
      coefficientNonzeroTorsionMorphism V S n ≫ (groupNonzeroTorsionTransportIso n e).hom.left := by
  apply (cancel_mono (nonzeroTorsionInclusion W n).left).mp
  have he := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n e)
  have hff := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n f)
  change _ ≫ _ = _ ≫ _ at he hff
  have ht := torsionTransport_coefficient S W V n e.hom f.hom hf
  change (torsionTransportIso f n).hom.left ≫ coefficientTorsionMorphism W S n =
    coefficientTorsionMorphism V S n ≫ (torsionTransportIso e n).hom.left at ht
  rw [Category.assoc, coefficientNonzeroTorsionMorphism_inclusion, ← Category.assoc, hff,
    Category.assoc, ht, ← Category.assoc, ← coefficientNonzeroTorsionMorphism_inclusion,
    Category.assoc, ← he, ← Category.assoc]

include hf in
/-- The cyclic quotient preserves compatibility of group transports with coefficients. -/
theorem groupCyclicTransport_coefficient (p : ℕ) [Fact p.Prime]
    [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))] :
    (groupCyclicParameterIso p f).hom.left ≫ coefficientScalarQuotientMorphism W S p =
      coefficientScalarQuotientMorphism V S p ≫ (groupCyclicParameterIso p e).hom.left := by
  apply (cancel_epi (scalarQuotientMap (V.map (algebraMap R S)) p).left).mp
  have he := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p e)
  have hff := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p f)
  change _ ≫ _ = _ ≫ _ at he hff
  rw [← Category.assoc, ← hff, Category.assoc,
    coefficientScalarQuotientMorphism_generators, ← Category.assoc,
    groupNonzeroTransport_coefficient S W V e f hf p, Category.assoc, he,
    ← Category.assoc, ← coefficientScalarQuotientMorphism_generators, Category.assoc]

/-- Actual coordinate-change transport on cyclic parameters commutes with coefficients. -/
theorem variableChangeCyclic_coefficient (p : ℕ) [Fact p.Prime]
    [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))] :
    (groupCyclicParameterIso p
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map (algebraMap R S)) (variableChange_map_equation S W V C h))).hom.left ≫
          coefficientScalarQuotientMorphism W S p =
      coefficientScalarQuotientMorphism V S p ≫
        (groupCyclicParameterIso p (variableChangeCongrOverIso W V C h)).hom.left :=
  groupCyclicTransport_coefficient S W V
    (variableChangeCongrOverIso W V C h)
    (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
      (C.map (algebraMap R S)) (variableChange_map_equation S W V C h))
    (variableChange_coefficient S W V C h) p

end WeierstrassCurve.CubicCharts
