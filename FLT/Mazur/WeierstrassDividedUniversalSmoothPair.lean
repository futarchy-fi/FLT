/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair
public import FLT.Mazur.WeierstrassDividedPairSecantGeometry

/-!
# The universal pair restricted to both full smooth charts

The tensor-pair smooth open maps openly into the product of the two full
relatively smooth divided charts, retaining both complete affine projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k)
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "P" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "v" => (V).ι ≫ s
local notation "O" => suppliedDividedSmoothInputOpen d a c
local notation "a'" => Spec.map (CommRingCat.ofHom (a).toRingHom)
local notation "c'" => Spec.map (CommRingCat.ofHom (c).toRingHom)
local notation "e" => dividedPairSpecIso W (π ^ k) d.b3 d.b4 d.b6

/-- Each tensor input restricted to its full relative smooth chart. -/
def universalDividedSmoothFactor (b : Bool) : (O).toScheme ⟶ (V).toScheme :=
  if b then
    Scheme.homOfLE (Spec (.of P)) (show O ≤ a' ⁻¹ᵁ V from inf_le_left) ≫ (a' ∣_ V)
  else
    Scheme.homOfLE (Spec (.of P)) (show O ≤ c' ⁻¹ᵁ V from inf_le_right) ≫ (c' ∣_ V)

/-- Both full affine projections are retained by restriction. -/
@[reassoc] theorem universalDividedSmoothFactor_inclusion (b : Bool) :
    universalDividedSmoothFactor d b ≫ (V).ι = (O).ι ≫ (if b then a' else c') := by
  cases b <;> simp only [universalDividedSmoothFactor, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The two restricted tensor factors have the same coefficient point. -/
@[reassoc] theorem universalDividedSmoothFactor_structure (b : Bool) :
    universalDividedSmoothFactor d b ≫ v =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [← Category.assoc, universalDividedSmoothFactor_inclusion]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Category.assoc,
    WeierstrassIntegralChart.specAlgHom_structure]

/-- The universal smooth tensor source maps to the product of the full smooth charts. -/
def universalDividedSmoothPair : (O).toScheme ⟶ pullback v v :=
  pullback.lift (universalDividedSmoothFactor d true) (universalDividedSmoothFactor d false)
    (by rw [universalDividedSmoothFactor_structure, universalDividedSmoothFactor_structure])

/-- The first full smooth input is the restricted first tensor projection. -/
@[reassoc] theorem universalDividedSmoothPair_fst :
    universalDividedSmoothPair d ≫ pullback.fst v v = universalDividedSmoothFactor d true :=
  pullback.lift_fst _ _ _

/-- The second full smooth input is the restricted second tensor projection. -/
@[reassoc] theorem universalDividedSmoothPair_snd :
    universalDividedSmoothPair d ≫ pullback.snd v v = universalDividedSmoothFactor d false :=
  pullback.lift_snd _ _ _

/-- Inclusion of the product of full smooth charts into the affine product. -/
def dividedSmoothProductInclusion : pullback v v ⟶ pullback s s :=
  pullback.map v v s s (V).ι (V).ι (𝟙 _) (by simp) (by simp)

instance dividedSmoothProductInclusion_open :
    IsOpenImmersion (dividedSmoothProductInclusion d) := by
  unfold dividedSmoothProductInclusion
  infer_instance

/-- In affine coordinates the universal smooth pair is exactly the tensor-product isomorphism. -/
@[reassoc] theorem universalDividedSmoothPair_inclusion :
    universalDividedSmoothPair d ≫ dividedSmoothProductInclusion d = (O).ι ≫ (e).inv := by
  apply pullback.hom_ext
  · simp only [dividedSmoothProductInclusion, pullback.map, Category.assoc,
      pullback.lift_fst, universalDividedSmoothPair_fst_assoc,
      universalDividedSmoothFactor_inclusion, ↓reduceIte, dividedPairSpecIso_fst]
  · simp only [dividedSmoothProductInclusion, pullback.map, Category.assoc,
      pullback.lift_snd, universalDividedSmoothPair_snd_assoc,
      universalDividedSmoothFactor_inclusion, Bool.false_eq_true, ↓reduceIte,
      dividedPairSpecIso_snd]

instance universalDividedSmoothPair_open : IsOpenImmersion (universalDividedSmoothPair d) := by
  have : IsOpenImmersion (universalDividedSmoothPair d ≫ dividedSmoothProductInclusion d) := by
    rw [universalDividedSmoothPair_inclusion]
    infer_instance
  exact IsOpenImmersion.of_comp _ (dividedSmoothProductInclusion d)

end FLT.Mazur.WeierstrassDividedDepth
