/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTorusSpecialization

/-!
# Actual torus action specialization on arbitrary test schemes

Both inputs are specialized by the actual Laurent and whole-model morphisms.
The comparison holds on the entire torus, including the identity.
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

variable {Z : Scheme} (p : Z ⟶ (MultiplicativeGroupScheme.gm T).left)
  (z : Z ⟶ coefficientShearGlued hπ data T (f r) j hj)
  (hpz : p ≫ Over.hom (MultiplicativeGroupScheme.gm T) =
    z ≫ coefficientShearGluedStructure hπ data T (f r) j hj)

include hpz in
/-- Both specialized inputs lie over the same original coefficient scheme. -/
theorem coefficientShearTorusSpecialization_pairCondition :
    (p ≫ L) ≫ tS = (z ≫ M) ≫ gS := by
  simp only [Category.assoc, nodalLaurentCoefficientMap_structure,
    coefficientShearSpecialization_structure]
  exact congrArg (· ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) hpz

/-- The complete domain map specializes both independently supplied inputs. -/
theorem coefficientShearTorusSpecialization_pairDomain :
    pullback.lift p z hpz ≫
        coefficientShearTorusSpecializationDomain hπ data S T f r j hj =
      pullback.lift (p ≫ L) (z ≫ M)
        (coefficientShearTorusSpecialization_pairCondition hπ data S T f r j hj p z hpz) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientShearTorusSpecializationDomain_parameter,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, coefficientShearTorusSpecializationDomain_model,
      pullback.lift_snd, pullback.lift_snd_assoc]

include hab in
/-- The actual action comparison evaluates on every full torus/model pair. -/
theorem coefficientShearTorusSpecialization_pairAction :
    (pullback.lift p z hpz ≫
        coefficientShearTorusAction hπ data T (f r) j hj b hb hv g3 g4 g6) ≫ M =
      pullback.lift (p ≫ L) (z ≫ M)
        (coefficientShearTorusSpecialization_pairCondition hπ data S T f r j hj p z hpz) ≫
          coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 := by
  rw [Category.assoc, coefficientShearTorusAction_specialization hπ data S T f r j hj a b hab,
    ← Category.assoc, coefficientShearTorusSpecialization_pairDomain]

end FLT.Mazur.WeierstrassDividedDepth
