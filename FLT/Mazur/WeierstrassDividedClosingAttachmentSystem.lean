/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingAttachmentRestriction
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Closing attachments over every arithmetic order

Each original closing pair and its transported twisted attachment form a
system with the original quotient arrows. Their constructed isomorphisms are
natural also for nonconsecutive orders, in both directions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)

/-- The entire original closing pair at all orders, for a fixed terminal branch. -/
def originalClosingAttachmentSystem (b : Bool) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ originalClosingAttachmentRestriction data H m j hj b)

variable [IsDomain R] (hπ : π ≠ 0)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The whole twisted target closing pair with its specified coefficient arrows. -/
def twistedClosingAttachmentSystem (b : Bool) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ twistedClosingAttachmentRestriction data H m j hj hπ u hu b)

/-- Whole closing-pair comparison as a natural transformation of the actual systems. -/
def closingAttachmentSystemHom (b : Bool) :
    originalClosingAttachmentSystem data H j hj b ⟶
      twistedClosingAttachmentSystem data H j hj hπ u hu b :=
  NatTrans.ofSequence (fun m ↦ (arithmeticClosingAttachmentIso data H m j hj u hu b).hom) (by
    intro m
    simpa only [originalClosingAttachmentSystem, twistedClosingAttachmentSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        closingAttachmentIso_restriction data H m j hj hπ u hu b)

/-- The constructed inverse is natural for the same arrows. -/
def closingAttachmentSystemInv (b : Bool) :
    twistedClosingAttachmentSystem data H j hj hπ u hu b ⟶
      originalClosingAttachmentSystem data H j hj b :=
  NatTrans.ofSequence (fun m ↦ (arithmeticClosingAttachmentIso data H m j hj u hu b).inv) (by
    intro m
    simpa only [originalClosingAttachmentSystem, twistedClosingAttachmentSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        closingAttachmentIso_inv_restriction data H m j hj hπ u hu b)

/-- The local attachment isomorphisms assemble into a genuine system isomorphism. -/
def closingAttachmentSystemIso (b : Bool) :
    originalClosingAttachmentSystem data H j hj b ≅
      twistedClosingAttachmentSystem data H j hj hπ u hu b where
  hom := closingAttachmentSystemHom data H j hj hπ u hu b
  inv := closingAttachmentSystemInv data H j hj hπ u hu b
  hom_inv_id := by ext m; exact (arithmeticClosingAttachmentIso data H m j hj u hu b).hom_inv_id
  inv_hom_id := by ext m; exact (arithmeticClosingAttachmentIso data H m j hj u hu b).inv_hom_id

/-- The system isomorphism uses exactly the previous full attachment comparison at each order. -/
@[simp] theorem closingAttachmentSystemIso_hom_app (b : Bool) (m : ℕ) :
    (closingAttachmentSystemIso data H j hj hπ u hu b).hom.app m =
      (arithmeticClosingAttachmentIso data H m j hj u hu b).hom := rfl

/-- Its inverse also uses the constructed full attachment inverse at every order. -/
@[simp] theorem closingAttachmentSystemIso_inv_app (b : Bool) (m : ℕ) :
    (closingAttachmentSystemIso data H j hj hπ u hu b).inv.app m =
      (arithmeticClosingAttachmentIso data H m j hj u hu b).inv := rfl

/-- Every nonadjacent original quotient arrow commutes with the full comparison. -/
@[reassoc] theorem closingAttachmentSystemIso_naturality
    (b : Bool) {a c : ℕ} (hac : a ≤ c) :
    (originalClosingAttachmentSystem data H j hj b).map (homOfLE hac) ≫
      (arithmeticClosingAttachmentIso data H c j hj u hu b).hom =
    (arithmeticClosingAttachmentIso data H a j hj u hu b).hom ≫
      (twistedClosingAttachmentSystem data H j hj hπ u hu b).map (homOfLE hac) :=
  (closingAttachmentSystemIso data H j hj hπ u hu b).hom.naturality (homOfLE hac)

/-- The inverse comparison preserves every nonadjacent original quotient arrow as well. -/
@[reassoc] theorem closingAttachmentSystemIso_inv_naturality
    (b : Bool) {a c : ℕ} (hac : a ≤ c) :
    (twistedClosingAttachmentSystem data H j hj hπ u hu b).map (homOfLE hac) ≫
      (arithmeticClosingAttachmentIso data H c j hj u hu b).inv =
    (arithmeticClosingAttachmentIso data H a j hj u hu b).inv ≫
      (originalClosingAttachmentSystem data H j hj b).map (homOfLE hac) :=
  (closingAttachmentSystemIso data H j hj hπ u hu b).inv.naturality (homOfLE hac)

end FLT.Mazur.WeierstrassDividedDepth
