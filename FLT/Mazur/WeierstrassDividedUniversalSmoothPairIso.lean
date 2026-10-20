/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUniversalSmoothPair

/-!
# The entire universal smooth tensor pair is the smooth-chart product

Construct the inverse using the tensor-product isomorphism. Both projections
land in their full smooth charts, so no input points are discarded.
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

/-- The product of full smooth charts retains its complete tensor coordinates. -/
def dividedSmoothProductToTensor : pullback v v ⟶ Spec (.of P) :=
  dividedSmoothProductInclusion d ≫ (e).hom

/-- The first tensor projection is the full first smooth input. -/
@[reassoc] theorem dividedSmoothProductToTensor_fst :
    dividedSmoothProductToTensor d ≫ a' = pullback.fst v v ≫ (V).ι := by
  rw [dividedSmoothProductToTensor, ← dividedPairSpecIso_fst, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [dividedSmoothProductInclusion, pullback.map, pullback.lift_fst]

/-- The second tensor projection is the full second smooth input. -/
@[reassoc] theorem dividedSmoothProductToTensor_snd :
    dividedSmoothProductToTensor d ≫ c' = pullback.snd v v ≫ (V).ι := by
  rw [dividedSmoothProductToTensor, ← dividedPairSpecIso_snd, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [dividedSmoothProductInclusion, pullback.map, pullback.lift_snd]

/-- Every point of the full smooth-chart product belongs to the tensor smooth open. -/
theorem dividedSmoothProductToTensor_range :
    Set.range (dividedSmoothProductToTensor d) ⊆ O := by
  rintro _ ⟨p, rfl⟩
  constructor
  · change a' (dividedSmoothProductToTensor d p) ∈ V
    rw [← Scheme.Hom.comp_apply, dividedSmoothProductToTensor_fst]
    exact (pullback.fst v v p).property
  · change c' (dividedSmoothProductToTensor d p) ∈ V
    rw [← Scheme.Hom.comp_apply, dividedSmoothProductToTensor_snd]
    exact (pullback.snd v v p).property

/-- The complete tensor-pair smooth open is the product of the full relative smooth charts. -/
def universalDividedSmoothPairIso : (O).toScheme ≅ pullback v v where
  hom := universalDividedSmoothPair d
  inv := IsOpenImmersion.lift (O).ι (dividedSmoothProductToTensor d) (by
    rw [Scheme.Opens.range_ι]
    exact dividedSmoothProductToTensor_range d)
  hom_inv_id := by
    apply (cancel_mono (O).ι).mp
    rw [Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp,
      dividedSmoothProductToTensor, ← Category.assoc, universalDividedSmoothPair_inclusion,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono (dividedSmoothProductInclusion d)).mp
    rw [Category.assoc, universalDividedSmoothPair_inclusion, ← Category.assoc,
      IsOpenImmersion.lift_fac, Category.id_comp, dividedSmoothProductToTensor,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The identification uses exactly the original universal smooth pair map. -/
theorem universalDividedSmoothPairIso_hom :
    (universalDividedSmoothPairIso d).hom = universalDividedSmoothPair d := rfl

end FLT.Mazur.WeierstrassDividedDepth
