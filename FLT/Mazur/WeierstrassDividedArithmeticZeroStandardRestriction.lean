/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroStandardEndpoints
public import FLT.Mazur.WeierstrassModificationXArithmeticPunctureRestriction
public import FLT.Mazur.WeierstrassModificationXInitialTerminalPunctureRestriction

/-!
# Both stage-zero standard endpoint comparisons commute with arithmetic restriction

The complete parameter changes between initial D(p) and terminal D(q)/D(p)
retain the actual quotient maps on both sides and the original Boolean label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (H : ArithmeticAtlasCoefficients data) (label : Bool)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "s" => π ^ start
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "c₀" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "c₁" => WeierstrassDilatation.arithmeticTerminalSmoothing π (m + 1) W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "hc" => WeierstrassDilatation.arithmeticTerminalSmoothing_restriction
  R π m W s (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "P" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f (q₁ s) (q₀ s)
    (AlgHom.commutes (restriction R π m) s) true))
local notation "T" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f c₁ c₀ hc label))
local notation "a₀" => zeroRetentionInitialTerminalStandardIso data m H label
local notation "a₁" => zeroRetentionInitialTerminalStandardIso data (m + 1) H label

attribute [local irreducible] arithmeticInitialPunctureIso initialTerminalArithmeticPunctureIso

/-- Both complete original standard endpoint parameters follow the actual quotient restriction. -/
@[reassoc] theorem zeroRetentionInitialTerminalStandardIso_restriction :
    P ≫ (a₁).hom = (a₀).hom ≫ T := by
  simp only [zeroRetentionInitialTerminalStandardIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, arithmeticInitialPunctureIso_inv_restriction,
    Category.assoc, initialTerminalArithmeticPunctureIso_restriction, ← Category.assoc]

/-- The inverse standard endpoint parameter change also retains both full coefficient maps. -/
@[reassoc] theorem zeroRetentionInitialTerminalStandardIso_inv_restriction :
    T ≫ (a₁).inv = (a₀).inv ≫ P := by
  have h := zeroRetentionInitialTerminalStandardIso_restriction data m H label
  have he := congrArg (fun g ↦ (a₀).inv ≫ g ≫ (a₁).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using he.symm

end FLT.Mazur.WeierstrassDividedDepth
