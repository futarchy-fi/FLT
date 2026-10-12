/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearSmoothSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearActionSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearTorusDomain

/-!
# Coefficient specialization of the full original torus action

The domain map uses the explicit Laurent coefficient map and the actual
whole-model specialization. Both independently constructed actions agree.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (j : ℕ) (hj : j ≤ n)
  (a : Sˣ) (b : Tˣ) (hab : Units.map f.toRingHom a = b)
local notation "V" => W.map (algebraMap R S)
local notation "U" => W.map (algebraMap R T)
variable (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0) (h6 : (W.map (algebraMap R S)).a₆ = 0)
  (hb : (b : T) = (W.map (algebraMap R T)).a₁ + 2 * f r)
  (hv : (f r) ^ 2 + (W.map (algebraMap R T)).a₁ * f r -
    (W.map (algebraMap R T)).a₂ = 0)
  (g3 : (W.map (algebraMap R T)).a₃ = 0)
  (g4 : (W.map (algebraMap R T)).a₄ = 0) (g6 : (W.map (algebraMap R T)).a₆ = 0)
local notation "gS" => coefficientShearGluedStructure hπ data S r j hj
local notation "gT" => coefficientShearGluedStructure hπ data T (f r) j hj
local notation "tS" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "tT" => Over.hom (MultiplicativeGroupScheme.gm T)
local notation "sS" => integralSmoothStructure V
local notation "sT" => integralSmoothStructure U
local notation "IS" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "IT" => rootShearTorusSmoothIso U (f r) b hb hv g3 g4 g6
local notation "L" => Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap f.toRingHom))
local notation "M" => coefficientShearSpecialization hπ data S T r (f r) j hj f
local notation "DS" => coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6
local notation "DT" => coefficientShearTorusDomainMap hπ data T (f r) j hj b hb hv g3 g4 g6

/-- The explicitly specialized torus and model inputs have the same coefficient map. -/
theorem coefficientShearTorusSpecialization_condition :
    (pullback.fst tT gT ≫ L) ≫ tS = (pullback.snd tT gT ≫ M) ≫ gS := by
  simp only [Category.assoc, nodalLaurentCoefficientMap_structure,
    coefficientShearSpecialization_structure]
  simpa only [Category.assoc] using
    congrArg (· ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
      (pullback.condition (f := tT) (g := gT))

/-- Coefficient specialization on the entire concrete torus action domain. -/
def coefficientShearTorusSpecializationDomain : pullback tT gT ⟶ pullback tS gS :=
  pullback.lift (pullback.fst tT gT ≫ L) (pullback.snd tT gT ≫ M)
    (coefficientShearTorusSpecialization_condition hπ data S T f r j hj)

local notation "D" => coefficientShearTorusSpecializationDomain hπ data S T f r j hj

/-- The original torus character is retained throughout the domain specialization. -/
@[reassoc] theorem coefficientShearTorusSpecializationDomain_parameter :
    D ≫ pullback.fst tS gS = pullback.fst tT gT ≫ L := pullback.lift_fst _ _ _

/-- The complete original model specializes by its actual coefficient morphism. -/
@[reassoc] theorem coefficientShearTorusSpecializationDomain_model :
    D ≫ pullback.snd tS gS = pullback.snd tT gT ≫ M := pullback.lift_snd _ _ _

include hab in
/-- The explicit torus specialization is the independently constructed smooth specialization. -/
@[reassoc] theorem coefficientShearTorusSpecializationDomain_smooth :
    D ≫ DS = DT ≫ coefficientShearSpecializationDomain hπ data S T r (f r) j hj f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientShearTorusDomainMap_parameter,
      coefficientShearSpecializationDomain_parameter,
      coefficientShearTorusSpecializationDomain_parameter_assoc,
      coefficientShearTorusDomainMap_parameter_assoc]
    rw [rootShearTorusSmoothIso_specialization W f r a b hab]
  · simp only [Category.assoc, coefficientShearTorusDomainMap_model,
      coefficientShearSpecializationDomain_model,
      coefficientShearTorusSpecializationDomain_model,
      coefficientShearTorusDomainMap_model_assoc]

include hab in
/-- The full explicit torus action commutes with the actual coefficient specialization. -/
@[reassoc] theorem coefficientShearTorusAction_specialization :
    coefficientShearTorusAction hπ data T (f r) j hj b hb hv g3 g4 g6 ≫ M =
      D ≫ coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 := by
  change (DT ≫ coefficientShearAction hπ data T (f r) j hj) ≫ M =
    D ≫ DS ≫ coefficientShearAction hπ data S r j hj
  rw [Category.assoc, coefficientShearAction_specialization,
    ← coefficientShearTorusSpecializationDomain_smooth_assoc hπ data S T f r j hj a b hab]

end FLT.Mazur.WeierstrassDividedDepth
