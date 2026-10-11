/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantHorizontalGlobalAction
public import FLT.Mazur.WeierstrassSmoothHorizontalActionAlgebra

/-!
# The concrete conic residue action is the single-step global action

The two constructed output residue maps retain every integral product
function. The integral comparison therefore specializes to the original
smooth and conic inputs, with no flatness assumption after specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassGlobalModification WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "C" => SmoothHorizontalResidueRing D
local notation "a" => smoothHorizontalLeft W (π ^ k)
local notation "c" => smoothHorizontalRight W (π ^ k)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "ha" => smoothHorizontalLeft_inclusion W (π ^ k)
local notation "hp" => smoothHorizontal_structure W (π ^ k)
local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "hc" => smoothHorizontalRight_contraction W (π ^ k)
local notation "hf" => smoothHorizontalInput_flat W (π ^ k)
local notation "T" => SecantPairRing W a c
local notation "α" => AlgHom.toRingHom
  (AlgHom.comp (secantPairPresentation W a c) (ordinaryChartAddition W false))
local notation "β" => AlgHom.toRingHom (AlgHom.comp (IsScalarTower.toAlgHom R S T) c)
local notation "p'" => Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ p
local notation "O" => LeftSmoothFractionActionOpen W (π ^ k) d.b3 d.b4 (π ^ k * d.b6)
  d.factor3 d.factor4 (smoothHorizontal_factor6 d) p' α β
  (secantPairSmooth_structure W a c p hp) (secantPairSmooth_addition W a c p ha hp)
  (coord W 2 0) (centerGenerators_mem W (π ^ k) 1)
  (secantHorizontalInput W (π ^ k) a c ψ) (secantHorizontal_beta W π a c ψ hc) 1
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap T O)) ≫
  Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "j" => originalFractionCoverMap W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ) (some 1)
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ j
local notation "act" => smoothPointAction W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)

/-- Each specialization of the original product retains the common coefficient point. -/
theorem smoothHorizontalGlobalInput_structure (e : S →+* C) :
    (Spec.map (CommRingCat.ofHom e) ≫ p) ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom e) ≫ b) ≫
        structureMap W (π ^ k) d.b3 d.b4 d.b6
          d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ) := by
  have h := fractionActionGlobalInput_structure W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ) p (c).toRingHom hp
    (coord W 2 0) (centerGenerators_mem W (π ^ k) 1) ψ hc
  have h' := congrArg (Spec.map (CommRingCat.ofHom e) ≫ ·) h
  dsimp only [originalFractionCoverMap, centerGenerators] at h' ⊢
  simp only [Category.assoc] at h' ⊢
  convert h' using 1
  rfl


/-- Any output specialization retaining the original product gives the actual global action. -/
theorem smoothHorizontalOutput_global (E : O →+* C) (e : S →+* C)
    (he : ∀ t, E (algebraMap S O t) = e t) :
    Spec.map (CommRingCat.ofHom (E.comp (smoothHorizontalActionLift d))) ≫ j =
      act (Spec.map (CommRingCat.ofHom e) ≫ p) (Spec.map (CommRingCat.ofHom e) ≫ b)
        (smoothHorizontalGlobalInput_structure D d hπ e) := by
  have he' : E.comp ((algebraMap T O).comp (algebraMap S T)) = e := by
    ext t
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact he t
  have hq : Spec.map (CommRingCat.ofHom E) ≫ q = Spec.map (CommRingCat.ofHom e) := by
    have h := congrArg (fun f : S →+* C => Spec.map (CommRingCat.ofHom f)) he'
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using h
  have h := secantHorizontalActionLift_global_specialize W π k d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 hπ a c p ha hp ψ hc hf (Spec.map (CommRingCat.ofHom E))
  have hqp : Spec.map (CommRingCat.ofHom E) ≫ q ≫ p =
      Spec.map (CommRingCat.ofHom e) ≫ p := by rw [← Category.assoc, hq]
  have hqb : Spec.map (CommRingCat.ofHom E) ≫ q ≫ b =
      Spec.map (CommRingCat.ofHom e) ≫ b := by rw [← Category.assoc, hq]
  simp only [Category.assoc] at hqp hqb
  simpa only [hqp, hqb, smoothHorizontalActionLift,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using h

local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

/-- The first original conic residue action is the actual global modified action. -/
theorem smoothHorizontalFirstAction_global :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalFirstAction D d hk0 hk hπ).toRingHom) ≫ j =
      act (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ p)
        (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ b)
        (smoothHorizontalGlobalInput_structure D d hπ (e₁).toRingHom) :=
  smoothHorizontalOutput_global D d hπ (smoothHorizontalFirstOutputResidue D d hk0 hk hπ)
    (e₁).toRingHom (smoothHorizontalFirstOutputResidue_base D d hk0 hk hπ)

/-- The opposite original conic residue action is the same actual global action. -/
theorem smoothHorizontalSecondAction_global :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalSecondAction D d hk0 hk hπ).toRingHom) ≫ j =
      act (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ p)
        (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ b)
        (smoothHorizontalGlobalInput_structure D d hπ (e₂).toRingHom) :=
  smoothHorizontalOutput_global D d hπ (smoothHorizontalSecondOutputResidue D d hk0 hk hπ)
    (e₂).toRingHom (smoothHorizontalSecondOutputResidue_base D d hk0 hk hπ)

end FLT.Mazur.WeierstrassIntegralChart
