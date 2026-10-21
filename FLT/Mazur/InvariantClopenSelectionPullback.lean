/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantClopenCoverSelection

/-!
# Naturality of selection on coordinated clopen covers

The fixed priority partition commutes with preimages. Hence local coefficients
that agree under a scheme map give global selected coefficients that agree
under that map. No stationarity or algebraization of formal sections is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantClopenCoverSelection
open InvariantOpenCoefficientRestriction InvariantOpenCoefficientGluing
open FiniteClopenPriorityCover
variable {D X E Y : Scheme.{0}} (p q : D ⟶ X) (p' q' : E ⟶ Y) {m : ℕ}
  (U : Fin m → X.Opens) (hi : ∀ i, p ⁻¹ᵁ U i = q ⁻¹ᵁ U i)
  (hc : ∀ i, IsClosed (U i : Set X)) (hcover : iSup U = ⊤)
  (V : Fin m → Y.Opens) (hi' : ∀ i, p' ⁻¹ᵁ V i = q' ⁻¹ᵁ V i)
  (hc' : ∀ i, IsClosed (V i : Set Y)) (hcover' : iSup V = ⊤)
  (f : Y ⟶ X) (hf : ∀ i, f ⁻¹ᵁ U i = V i)
  (v : ∀ i, coefficients p q (U i) (hi i))
  (w : ∀ i, coefficients p' q' (V i) (hi' i))
local notation "P" i:max => (piece U hc i : X.Opens)
local notation "ιP" i:max => Scheme.Opens.ι (P i)
local notation "Q" i:max => (piece V hc' i : Y.Opens)
local notation "ιQ" i:max => Scheme.Opens.ι (Q i)

include hf in
/-- The full selected sections commute with maps preserving the named domains and coefficients. -/
theorem select_pullback
    (hv : ∀ i, (f.resLE (U i) (V i) (hf i).ge).appTop (v i).val = (w i).val) :
    f.appTop (select p q U hi hc hcover v).val =
      (select p' q' V hi' hc' hcover' w).val := by
  have hP (i : Fin m) : f ⁻¹ᵁ P i = Q i :=
    SetLike.coe_injective (preimage_piece U hc V hc' f
      (fun j ↦ congrArg SetLike.coe (hf j)) i)
  apply section_ext (fun i ↦ Q i) (by rw [iSup_piece, hcover'])
  intro i
  rw [select_piece]
  let g := f.resLE (P i) (Q i) (hP i).ge
  have hg : g ≫ (ιP i) = (ιQ i) ≫ f := Scheme.Hom.resLE_comp_ι _ _
  change ((ιQ i) ≫ f).appTop _ = _
  rw [← hg]
  change g.appTop ((ιP i).appTop _) = _
  rw [select_piece]
  have he : g ≫ X.homOfLE (piece_le U hc i) =
      Y.homOfLE (piece_le V hc' i) ≫ f.resLE (U i) (V i) (hf i).ge := by
    apply (cancel_mono (U i).ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, hg, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  change (g ≫ X.homOfLE (piece_le U hc i)).appTop _ = _
  rw [he]
  change (Y.homOfLE (piece_le V hc' i)).appTop
    ((f.resLE (U i) (V i) (hf i).ge).appTop (v i).val) = _
  rw [hv i]

end FLT.Mazur.InvariantClopenCoverSelection
