/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentOverlapEquiv
public import FLT.Mazur.NodeTangentCoefficientCover
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The original quadratic Cech scheme and its two Galois branches

The product decomposition of the actual tensor algebra gives a coproduct
isomorphism onto the actual scheme pullback. Its two projections are
identity/identity and identity/conjugation, respectively.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "σ" => nodeTangentCoverConjugation W

/-- The identity branch lands in the original coefficient fiber product. -/
def nodeTangentCechIdentity : Spec (.of S) ⟶ pullback q q :=
  Spec.map (CommRingCat.ofHom (nodeTangentOverlapIdentity W).toRingHom) ≫
    (pullbackSpecIso R S S).inv

/-- The conjugate branch lands in that same original fiber product. -/
def nodeTangentCechConjugate : Spec (.of S) ⟶ pullback q q :=
  Spec.map (CommRingCat.ofHom (nodeTangentOverlapConjugate W).toRingHom) ≫
    (pullbackSpecIso R S S).inv

@[reassoc] theorem nodeTangentCechIdentity_fst :
    nodeTangentCechIdentity W ≫ pullback.fst q q = 𝟙 _ := by
  unfold nodeTangentCover
  rw [nodeTangentCechIdentity, Category.assoc, pullbackSpecIso_inv_fst,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change x * 1 = x
  exact mul_one x

@[reassoc] theorem nodeTangentCechIdentity_snd :
    nodeTangentCechIdentity W ≫ pullback.snd q q = 𝟙 _ := by
  unfold nodeTangentCover
  rw [nodeTangentCechIdentity, Category.assoc, pullbackSpecIso_inv_snd,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change 1 * x = x
  exact one_mul x

@[reassoc] theorem nodeTangentCechConjugate_fst :
    nodeTangentCechConjugate W ≫ pullback.fst q q = 𝟙 _ := by
  unfold nodeTangentCover
  rw [nodeTangentCechConjugate, Category.assoc, pullbackSpecIso_inv_fst,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change x * nodeTangentConjugation W 1 = x
  rw [map_one, mul_one]

@[reassoc] theorem nodeTangentCechConjugate_snd :
    nodeTangentCechConjugate W ≫ pullback.snd q q = σ := by
  unfold nodeTangentCover
  rw [nodeTangentCechConjugate, Category.assoc, pullbackSpecIso_inv_snd,
    nodeTangentCoverConjugation, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change 1 * nodeTangentConjugation W x = nodeTangentConjugation W x
  exact one_mul _

/-- The full original Cech scheme splits into these two actual branches. -/
def nodeTangentCechIso [Nontrivial R] (hb : IsUnit W.b₂) :
    Spec (.of S) ⨿ Spec (.of S) ≅ pullback q q :=
  asIso (coprodSpec S S) ≪≫
    Scheme.Spec.mapIso (nodeTangentOverlapEquiv W hb).toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso R S S).symm

/-- The first summand is precisely the identity branch, with the original projections. -/
@[reassoc] theorem nodeTangentCechIso_inl [Nontrivial R] (hb : IsUnit W.b₂) :
    coprod.inl ≫ (nodeTangentCechIso W hb).hom = nodeTangentCechIdentity W := by
  simp only [nodeTangentCechIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    coprodSpec_inl_assoc, nodeTangentCechIdentity]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc]
  rfl

/-- The second summand is precisely the conjugate branch. -/
@[reassoc] theorem nodeTangentCechIso_inr [Nontrivial R] (hb : IsUnit W.b₂) :
    coprod.inr ≫ (nodeTangentCechIso W hb).hom = nodeTangentCechConjugate W := by
  simp only [nodeTangentCechIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    coprodSpec_inr_assoc, nodeTangentCechConjugate]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc]
  rfl

/-- Both branches detect morphisms on the entire original Cech scheme, for any target. -/
theorem nodeTangentCech_hom_ext [Nontrivial R] (hb : IsUnit W.b₂)
    {Y : Scheme.{u}} {f g : pullback q q ⟶ Y}
    (hi : nodeTangentCechIdentity W ≫ f = nodeTangentCechIdentity W ≫ g)
    (hc : nodeTangentCechConjugate W ≫ f = nodeTangentCechConjugate W ≫ g) : f = g := by
  apply (cancel_epi (nodeTangentCechIso W hb).hom).mp
  apply coprod.hom_ext
  · simpa only [nodeTangentCechIso_inl_assoc] using hi
  · simpa only [nodeTangentCechIso_inr_assoc] using hc

end FLT.Mazur
