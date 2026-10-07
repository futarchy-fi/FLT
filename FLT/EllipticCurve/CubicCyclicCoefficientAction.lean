/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCoefficientAction
/-! # Coefficient actions on torsion and cyclic parameters

The coefficient pullback squares induce actions on full torsion, nonzero
torsion, and cyclic parameters. The inclusions and scalar quotient respect
these actions. Conjugacy of curve maps therefore passes to cyclic transport.
For a quadratic root algebra this is the actual covering involution. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S] (σ : S →ₐ[R] S)
variable [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
variable [W.IsElliptic]

/-- The coefficient action on the actual full torsion scheme. -/
def coefficientTorsionEnd (n : ℕ) :
    (torsionModel (W.map (algebraMap R S)) n).left ⟶
      (torsionModel (W.map (algebraMap R S)) n).left :=
  (coefficientTorsion_isPullback W S n).lift (coefficientTorsionMorphism W S n)
    ((torsionModel (W.map (algebraMap R S)) n).hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by rw [Category.assoc, coefficientEnd_base, coefficientTorsionMorphism_toBase])

/-- The torsion action fixes the original torsion projection. -/
@[reassoc (attr := simp)]
theorem coefficientTorsionEnd_coefficient (n : ℕ) :
    coefficientTorsionEnd W S σ n ≫ coefficientTorsionMorphism W S n =
      coefficientTorsionMorphism W S n :=
  (coefficientTorsion_isPullback W S n).lift_fst _ _ _

/-- The torsion action induces the coefficient-base action. -/
@[reassoc (attr := simp)]
theorem coefficientTorsionEnd_toBase (n : ℕ) :
    coefficientTorsionEnd W S σ n ≫ (torsionModel (W.map (algebraMap R S)) n).hom =
      (torsionModel (W.map (algebraMap R S)) n).hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientTorsion_isPullback W S n).lift_snd _ _ _

/-- The torsion action agrees with the global curve action after inclusion. -/
theorem coefficientTorsionEnd_inclusion (n : ℕ) :
    coefficientTorsionEnd W S σ n ≫ (torsionInclusion (W.map (algebraMap R S)) n).left =
      (torsionInclusion (W.map (algebraMap R S)) n).left ≫ coefficientEndMorphism W S σ := by
  apply (coefficientMorphism_isPullback W S).hom_ext
  · rw [Category.assoc, ← coefficientTorsionMorphism_inclusion, ← Category.assoc,
      coefficientTorsionEnd_coefficient, coefficientTorsionMorphism_inclusion,
      Category.assoc, coefficientEndMorphism_coefficient]
  · have hi : (torsionInclusion (W.map (algebraMap R S)) n).left ≫
        toBase (W.map (algebraMap R S)) = (torsionModel (W.map (algebraMap R S)) n).hom :=
      (torsionInclusion (W.map (algebraMap R S)) n).w
    rw [Category.assoc, hi, coefficientTorsionEnd_toBase, Category.assoc,
      coefficientEndMorphism_toBase, ← Category.assoc, hi]

/-- The coefficient action on nonzero torsion. -/
def coefficientNonzeroEnd (n : ℕ) [NeZero n] :
    (nonzeroTorsionModel (W.map (algebraMap R S)) n).left ⟶
      (nonzeroTorsionModel (W.map (algebraMap R S)) n).left :=
  (coefficientNonzeroTorsion_isPullback W S n).lift (coefficientNonzeroTorsionMorphism W S n)
    ((nonzeroTorsionModel (W.map (algebraMap R S)) n).hom ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by
      rw [Category.assoc, coefficientEnd_base]
      exact (coefficientNonzeroTorsion_isPullback W S n).w)

/-- The nonzero action fixes the original coefficient projection. -/
@[reassoc (attr := simp)]
theorem coefficientNonzeroEnd_coefficient (n : ℕ) [NeZero n] :
    coefficientNonzeroEnd W S σ n ≫ coefficientNonzeroTorsionMorphism W S n =
      coefficientNonzeroTorsionMorphism W S n :=
  (coefficientNonzeroTorsion_isPullback W S n).lift_fst _ _ _

/-- The nonzero action lies over the coefficient action. -/
@[reassoc (attr := simp)]
theorem coefficientNonzeroEnd_toBase (n : ℕ) [NeZero n] :
    coefficientNonzeroEnd W S σ n ≫ (nonzeroTorsionModel (W.map (algebraMap R S)) n).hom =
      (nonzeroTorsionModel (W.map (algebraMap R S)) n).hom ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientNonzeroTorsion_isPullback W S n).lift_snd _ _ _

/-- The nonzero action agrees with the action on full torsion. -/
theorem coefficientNonzeroEnd_inclusion (n : ℕ) [NeZero n] :
    coefficientNonzeroEnd W S σ n ≫ (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left =
      (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left ≫ coefficientTorsionEnd
        W S σ n := by
  apply (coefficientTorsion_isPullback W S n).hom_ext
  · rw [Category.assoc, ← coefficientNonzeroTorsionMorphism_inclusion, ← Category.assoc,
      coefficientNonzeroEnd_coefficient, coefficientNonzeroTorsionMorphism_inclusion,
      Category.assoc, coefficientTorsionEnd_coefficient]
  · have hi := (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).w
    rw [Category.assoc, hi, coefficientNonzeroEnd_toBase, Category.assoc,
      coefficientTorsionEnd_toBase, ← Category.assoc, hi]

variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))]

/-- The coefficient action on the actual cyclic-parameter scheme. -/
def coefficientCyclicEnd :
    (scalarQuotientModel (W.map (algebraMap R S)) p).left ⟶
      (scalarQuotientModel (W.map (algebraMap R S)) p).left :=
  (coefficientScalarQuotient_isPullback W S p).lift (coefficientScalarQuotientMorphism W S p)
    ((scalarQuotientModel (W.map (algebraMap R S)) p).hom ≫ Spec.map (CommRingCat.ofHom
      σ.toRingHom))
    (by rw [Category.assoc, coefficientEnd_base, coefficientScalarQuotientMorphism_toBase])

/-- The cyclic action fixes the original cyclic parameter. -/
@[reassoc (attr := simp)]
theorem coefficientCyclicEnd_coefficient :
    coefficientCyclicEnd W S σ p ≫ coefficientScalarQuotientMorphism W S p =
      coefficientScalarQuotientMorphism W S p :=
  (coefficientScalarQuotient_isPullback W S p).lift_fst _ _ _

/-- The cyclic action lies over the coefficient action. -/
@[reassoc (attr := simp)]
theorem coefficientCyclicEnd_toBase :
    coefficientCyclicEnd W S σ p ≫ (scalarQuotientModel (W.map (algebraMap R S)) p).hom =
      (scalarQuotientModel (W.map (algebraMap R S)) p).hom ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientScalarQuotient_isPullback W S p).lift_snd _ _ _

/-- The cyclic action agrees with the action on nonzero generators. -/
theorem coefficientCyclicEnd_quotient :
    coefficientNonzeroEnd W S σ p ≫ (scalarQuotientMap (W.map (algebraMap R S)) p).left =
      (scalarQuotientMap (W.map (algebraMap R S)) p).left ≫ coefficientCyclicEnd W S σ p := by
  apply (coefficientScalarQuotient_isPullback W S p).hom_ext
  · rw [Category.assoc, coefficientScalarQuotientMorphism_generators, ← Category.assoc,
      coefficientNonzeroEnd_coefficient, ← coefficientScalarQuotientMorphism_generators,
      Category.assoc, coefficientCyclicEnd_coefficient]
  · have hi := (scalarQuotientMap (W.map (algebraMap R S)) p).w
    rw [Category.assoc, hi, coefficientNonzeroEnd_toBase, Category.assoc,
      coefficientCyclicEnd_toBase, ← Category.assoc, hi]

section Transport
variable (V : WeierstrassCurve R) [V.IsElliptic]
variable (e f : groupModel (V.map (algebraMap R S)) ≅ groupModel (W.map (algebraMap R S)))
variable [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
variable (he : coefficientEndMorphism V S σ ≫ e.hom.left = f.hom.left ≫
  coefficientEndMorphism W S σ)

omit [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))] in
include he in
/-- Conjugacy of curve maps restricts to full torsion. -/
theorem coefficientEnd_torsionTransport (n : ℕ) :
    coefficientTorsionEnd V S σ n ≫ (torsionTransportIso e n).hom.left =
      (torsionTransportIso f n).hom.left ≫ coefficientTorsionEnd W S σ n := by
  apply (cancel_mono (torsionInclusion (W.map (algebraMap R S)) n).left).mp
  have h₁ := congrArg Over.Hom.left (torsionTransport_inclusion e.hom n)
  have h₂ := congrArg Over.Hom.left (torsionTransport_inclusion f.hom n)
  change (torsionTransportIso e n).hom.left ≫ _ = _ ≫ e.hom.left at h₁
  change (torsionTransportIso f n).hom.left ≫ _ = _ ≫ f.hom.left at h₂
  rw [Category.assoc, h₁, ← Category.assoc, coefficientTorsionEnd_inclusion,
    Category.assoc, he, ← Category.assoc, ← h₂, Category.assoc,
    ← coefficientTorsionEnd_inclusion, ← Category.assoc]

omit [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))] in
include he in
/-- Conjugacy restricts to nonzero torsion. -/
theorem coefficientEnd_nonzeroTransport (n : ℕ) [NeZero n] :
    coefficientNonzeroEnd V S σ n ≫ (groupNonzeroTorsionTransportIso n e).hom.left =
      (groupNonzeroTorsionTransportIso n f).hom.left ≫ coefficientNonzeroEnd W S σ n := by
  apply (cancel_mono (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left).mp
  have h₁ := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n e)
  have h₂ := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n f)
  change _ ≫ _ = _ ≫ _ at h₁ h₂
  rw [Category.assoc, h₁, ← Category.assoc, coefficientNonzeroEnd_inclusion,
    Category.assoc, coefficientEnd_torsionTransport W S σ V e f he n,
    ← Category.assoc, ← h₂, Category.assoc, ← coefficientNonzeroEnd_inclusion,
    ← Category.assoc]

include he in
/-- Conjugacy descends to the scalar quotient. -/
theorem coefficientEnd_cyclicTransport :
    coefficientCyclicEnd V S σ p ≫ (groupCyclicParameterIso p e).hom.left =
      (groupCyclicParameterIso p f).hom.left ≫ coefficientCyclicEnd W S σ p := by
  apply (cancel_epi (scalarQuotientMap (V.map (algebraMap R S)) p).left).mp
  have h₁ := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p e)
  have h₂ := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p f)
  change _ ≫ _ = _ ≫ _ at h₁ h₂
  rw [← Category.assoc, ← coefficientCyclicEnd_quotient, Category.assoc, ← h₁,
    ← Category.assoc, coefficientEnd_nonzeroTransport W S σ V e f he p,
    Category.assoc, coefficientCyclicEnd_quotient, ← Category.assoc, h₂, Category.assoc]
end Transport

/-- Coefficient action conjugates the actual cyclic coordinate transport. -/
theorem coefficientEnd_variableChange_cyclic (V : WeierstrassCurve R) [V.IsElliptic]
    (C : VariableChange S) (h : C • W.map (algebraMap R S) = V.map (algebraMap R S)) :
    coefficientCyclicEnd V S σ p ≫
        (groupCyclicParameterIso p (variableChangeCongrOverIso (W.map (algebraMap R S))
          (V.map (algebraMap R S)) C h)).hom.left =
      (groupCyclicParameterIso p (variableChangeCongrOverIso (W.map (algebraMap R S))
        (V.map (algebraMap R S)) (C.map σ.toRingHom)
          (coefficientEnd_variableChange_equation W S σ V C h))).hom.left ≫
            coefficientCyclicEnd W S σ p :=
  coefficientEnd_cyclicTransport W S σ p V _ _ (coefficientEnd_variableChange W S σ V C h)

section Quadratic
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]

omit [Fact (IsUnit (2 : R))] in
/-- The cyclic pullback comparison preserves the covering base. -/
theorem quadraticCyclicPullbackIso_snd :
    (quadraticCyclicPullbackIso d W p).hom ≫
      pullback.snd (scalarQuotientModel W p).hom (quadraticEtaleCover d) =
        (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).hom :=
  (coefficientScalarQuotientComparison W (QuadraticEtaleRing d) p).w

omit [Fact (IsUnit (2 : R))] in
/-- The root coefficient action is the covering involution used in cyclic descent. -/
theorem coefficientCyclicEnd_quadratic :
    coefficientCyclicEnd W (QuadraticEtaleRing d) (quadraticEtaleNeg d) p =
      quadraticCyclicSign d W p := by
  apply (cancel_mono (quadraticCyclicPullbackIso d W p).hom).mp
  rw [quadraticCyclicSign]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, quadraticCyclicPullbackIso_fst, coefficientCyclicEnd_coefficient,
      Category.assoc, quadraticPullbackSign_fst, quadraticCyclicPullbackIso_fst]
  · rw [Category.assoc, quadraticCyclicPullbackIso_snd, coefficientCyclicEnd_toBase,
      Category.assoc, quadraticPullbackSign_snd, ← Category.assoc,
      quadraticCyclicPullbackIso_snd]
    rfl
end Quadratic



end WeierstrassCurve.CubicCharts
