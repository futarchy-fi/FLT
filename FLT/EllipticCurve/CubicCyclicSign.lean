/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicTransportFunctor
public import FLT.EllipticCurve.CubicLegendreSign

/-! # Cyclic transport is independent of elliptic negation

Negation is the scalar -1 on the represented torsion scheme.
Group-scheme isomorphisms differing by negation therefore induce the
same map on the prime cyclic-parameter quotient. In particular, the
local Legendre swap and reciprocal transports are independent of the
sign of their chosen square root. The cyclic construction here uses
the existing noetherian domain hypotheses and invertible prime level.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
section General
variable (W : WeierstrassCurve R) [W.IsElliptic] (n : ℕ) [NeZero n]

/-- Multiplication by minus one is inversion on the torsion group scheme. -/
theorem torsionScalarIso_neg_one :
    (torsionScalarIso W n (-1)).hom = (𝟙 (torsionModel W n))⁻¹ := by
  let a := ((-1 : (ZMod n)ˣ) : ZMod n).val
  have ha : a + 1 ≡ 0 [MOD n] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    simp [a]
  have hp : (𝟙 (torsionModel W n)) ^ (a + 1) = 1 :=
    (pow_eq_pow_of_modEq ha (torsionPoint_pow_eq_one W n (𝟙 _))).trans (pow_zero _)
  rw [pow_succ] at hp
  change (𝟙 (torsionModel W n)) ^ a = (𝟙 (torsionModel W n))⁻¹
  calc
    _ = ((𝟙 (torsionModel W n)) ^ a * 𝟙 _) * (𝟙 (torsionModel W n))⁻¹ := by
      simp only [_root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
    _ = _ := by rw [hp, _root_.one_mul]

/-- The scalar minus one restricts actual elliptic negation. -/
theorem torsionScalarIso_neg_one_inclusion :
    (torsionScalarIso W n (-1)).hom ≫ torsionInclusion W n =
      torsionInclusion W n ≫ negationOver W := by
  rw [torsionScalarIso_neg_one, GrpObj.inv_comp, Category.id_comp]
  change _ = torsionInclusion W n ≫ GrpObj.inv
  rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]

variable {W}
variable {V : WeierstrassCurve R} [V.IsElliptic]

/-- Curve isomorphisms differing by negation differ by minus one on torsion. -/
theorem torsionTransportIso_neg
    (e f : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
    (h : f.hom = e.hom ≫ negationOver W) :
    (torsionTransportIso f n).hom =
      (torsionTransportIso e n).hom ≫ (torsionScalarIso W n (-1)).hom := by
  apply (cancel_mono (torsionInclusion W n)).mp
  change torsionTransport f.hom n ≫ torsionInclusion W n =
    (torsionTransport e.hom n ≫ (torsionScalarIso W n (-1)).hom) ≫ torsionInclusion W n
  rw [torsionTransport_inclusion, Category.assoc, torsionScalarIso_neg_one_inclusion,
    ← Category.assoc, torsionTransport_inclusion, Category.assoc, h]

/-- A group-scheme isomorphism restricts to an isomorphism of nonzero torsion. -/
def groupNonzeroTorsionTransportIso (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    nonzeroTorsionModel V n ≅ nonzeroTorsionModel W n :=
  nonzeroTorsionTransportIso n (torsionTransportIso e n)
    (torsionIso_zero n (torsionTransportIso e n))

/-- The nonzero transport is the restriction of the full torsion transport. -/
theorem groupNonzeroTorsionTransportIso_hom (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    (groupNonzeroTorsionTransportIso n e).hom =
      nonzeroTorsionTransport (V := V) (W := W) n (torsionTransportIso e n)
        (torsionIso_zero n (torsionTransportIso e n)) := rfl

attribute [local irreducible] groupNonzeroTorsionTransportIso

/-- Nonzero transport commutes with the inclusion into full torsion. -/
theorem groupNonzeroTorsionTransportIso_inclusion (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    (groupNonzeroTorsionTransportIso n e).hom ≫ nonzeroTorsionInclusion W n =
      nonzeroTorsionInclusion V n ≫ (torsionTransportIso e n).hom := by
  rw [groupNonzeroTorsionTransportIso_hom]
  exact nonzeroTorsionTransport_inclusion n (torsionTransportIso e n)
    (torsionIso_zero n (torsionTransportIso e n))

/-- The nonzero transport intertwines every scalar action. -/
theorem groupNonzeroTorsionTransportIso_scalar (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction V n a).inv ≫ (groupNonzeroTorsionTransportIso n e).hom =
      (groupNonzeroTorsionTransportIso n e).hom ≫ (nonzeroTorsionScalarAction W n a).inv := by
  rw [nonzeroTorsionScalarAction_inv, nonzeroTorsionScalarAction_inv,
    groupNonzeroTorsionTransportIso_hom]
  exact nonzeroTorsionTransport_scalar (V := V) (W := W) n (torsionTransportIso e n)
    (torsionIso_zero n (torsionTransportIso e n)) a⁻¹

/-- Negation changes the nonzero torsion transport by the scalar minus one. -/
theorem groupNonzeroTorsionTransportIso_neg (e f : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
    (h : f.hom = e.hom ≫ negationOver W) :
    (groupNonzeroTorsionTransportIso n f).hom =
      (groupNonzeroTorsionTransportIso n e).hom ≫ (nonzeroTorsionScalarAction W n (-1)).hom := by
  apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
  rw [groupNonzeroTorsionTransportIso_inclusion, Category.assoc,
    nonzeroTorsionScalarAction_hom, nonzeroTorsionScalarHom_inclusion,
    ← Category.assoc, groupNonzeroTorsionTransportIso_inclusion, Category.assoc,
    torsionTransportIso_neg n e f h]

variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
omit [NeZero n] in
/-- The cyclic-parameter isomorphism induced by a group-scheme isomorphism. -/
def groupCyclicParameterIso (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    scalarQuotientModel V p ≅ scalarQuotientModel W p :=
  scalarQuotientTransportIso p (groupNonzeroTorsionTransportIso p e)
    (groupNonzeroTorsionTransportIso_scalar p e)

omit [NeZero n] [Fact p.Prime] in
/-- Cyclic transport commutes with forgetting the torsion generator. -/
theorem groupCyclicParameterIso_quotient (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    (groupNonzeroTorsionTransportIso p e).hom ≫ scalarQuotientMap W p =
      scalarQuotientMap V p ≫ (groupCyclicParameterIso p e).hom := by
  dsimp only [groupCyclicParameterIso]
  exact scalarQuotientTransportIso_quotient (V := V) (W := W) p
    (groupNonzeroTorsionTransportIso p e) (groupNonzeroTorsionTransportIso_scalar p e)

omit [NeZero n] in
/-- Curve transports differing by negation induce identical cyclic transport. -/
theorem groupCyclicParameterIso_neg (e f : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
    (h : f.hom = e.hom ≫ negationOver W) :
    groupCyclicParameterIso p e = groupCyclicParameterIso p f :=
  scalarQuotientTransportIso_eq_of_scalar p
    (groupNonzeroTorsionTransportIso p e) (groupNonzeroTorsionTransportIso p f)
    (groupNonzeroTorsionTransportIso_scalar p e) (groupNonzeroTorsionTransportIso_scalar p f)
    (-1) (groupNonzeroTorsionTransportIso_neg p e f h)

end General

variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- The cyclic-parameter transport associated to a local Legendre swap. -/
def legendreSwapCyclicParameterIso (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1)
    [(legendreCurve l).IsElliptic] [(legendreCurve (1 - l)).IsElliptic] :
    scalarQuotientModel (legendreCurve (1 - l)) p ≅ scalarQuotientModel (legendreCurve l) p :=
  groupCyclicParameterIso p (legendreSwapOverIso l u hu)

/-- The cyclic-parameter transport associated to a local reciprocal change. -/
def legendreReciprocalCyclicParameterIso (l u : Rˣ) (hu : (u : R) ^ 2 = l)
    [(legendreCurve (l : R)).IsElliptic]
    [(legendreCurve ((l⁻¹ : Rˣ) : R)).IsElliptic] :
    scalarQuotientModel (legendreCurve ((l⁻¹ : Rˣ) : R)) p ≅
      scalarQuotientModel (legendreCurve (l : R)) p :=
  groupCyclicParameterIso p (legendreReciprocalOverIso l u hu)

/-- The cyclic swap transport is independent of the square-root sign. -/
theorem legendreSwapCyclicParameterIso_neg (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1)
    [(legendreCurve l).IsElliptic] [(legendreCurve (1 - l)).IsElliptic] :
    legendreSwapCyclicParameterIso p l (-u)
        (by simpa only [Units.val_neg, neg_sq] using hu) =
      legendreSwapCyclicParameterIso p l u hu := by
  exact (groupCyclicParameterIso_neg (V := legendreCurve (1 - l)) (W := legendreCurve l) p
    (legendreSwapOverIso l u hu)
    (legendreSwapOverIso l (-u) (by simpa only [Units.val_neg, neg_sq] using hu))
    (legendreSwapOverIso_neg l u hu)).symm

/-- The cyclic reciprocal transport is independent of the square-root sign. -/
theorem legendreReciprocalCyclicParameterIso_neg (l u : Rˣ) (hu : (u : R) ^ 2 = l)
    [(legendreCurve (l : R)).IsElliptic]
    [(legendreCurve ((l⁻¹ : Rˣ) : R)).IsElliptic] :
    legendreReciprocalCyclicParameterIso p l (-u)
        (by simpa only [Units.val_neg, neg_sq] using hu) =
      legendreReciprocalCyclicParameterIso p l u hu := by
  exact (groupCyclicParameterIso_neg
    (V := legendreCurve ((l⁻¹ : Rˣ) : R)) (W := legendreCurve (l : R)) p
    (legendreReciprocalOverIso l u hu)
    (legendreReciprocalOverIso l (-u) (by simpa only [Units.val_neg, neg_sq] using hu))
    (legendreReciprocalOverIso_neg l u hu)).symm

end WeierstrassCurve.CubicCharts
