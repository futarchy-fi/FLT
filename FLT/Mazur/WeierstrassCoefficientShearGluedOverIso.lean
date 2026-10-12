/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearGluing

/-!
# Reconstruction of the full sheared model over its coefficient scheme

The complete equation comparison is an isomorphism over the coefficient ring.
This packages its two structural legs for normalization and pinching diagrams.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)
local notation "E" => coefficientShearGluedIso hπ data S r t ht
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (finiteGlobalStructure hπ data t ht)
local notation "q" => coefficientShearGluedStructure hπ data S r t ht

/-- The full equation reconstruction as an isomorphism over the actual coefficient scheme. -/
def coefficientShearGluedOverIso : Over.mk q ≅ Over.mk p :=
  Over.isoMk E rfl

/-- Reconstruction on underlying schemes is exactly the original full chart comparison. -/
@[simp] theorem coefficientShearGluedOverIso_hom_left :
    (coefficientShearGluedOverIso hπ data S r t ht).hom.left = (E).hom := rfl

/-- The inverse on underlying schemes is the inverse original chart comparison. -/
@[simp] theorem coefficientShearGluedOverIso_inv_left :
    (coefficientShearGluedOverIso hπ data S r t ht).inv.left = (E).inv := rfl

/-- An over-morphism comparison reduces to its complete reconstruction on underlying schemes. -/
theorem coefficientShearGluedOverIso_hom_ext {X : Over (Spec (.of S))}
    (f g : X ⟶ Over.mk q)
    (h : f.left ≫ (E).hom = g.left ≫ (E).hom) : f = g := by
  apply Over.OverMorphism.ext
  exact (cancel_mono (E).hom).mp h

end FLT.Mazur.WeierstrassDividedDepth
