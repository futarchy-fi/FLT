/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteClopenPriorityCover
public import FLT.Mazur.InvariantClopenSectionExtension

/-!
# Selecting full invariant sections on a finite clopen cover

A fixed disjoint refinement glues independently chosen invariant local sections.
No overlap equality is assumed. If the original sections have the same full
boundary value, the selected global section retains that value everywhere.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantClopenCoverSelection
open InvariantOpenCoefficientRestriction InvariantOpenCoefficientGluing
open FiniteClopenPriorityCover SchemeClopenSectionExtension
open SchemeEffectiveEpiSections IdealSheafClosedTransitions
variable {D X : Scheme.{0}} (p q : D ⟶ X) {m : ℕ} (U : Fin m → X.Opens)
  (hi : ∀ i, p ⁻¹ᵁ U i = q ⁻¹ᵁ U i) (hc : ∀ i, IsClosed (U i : Set X))
local notation "P" i:max => (piece U hc i : X.Opens)
local notation "ιP" i:max => Scheme.Opens.ι (P i)

include hi in
/-- The fixed disjoint pieces retain all relation arrows. -/
theorem piece_invariant (i : Fin m) : p ⁻¹ᵁ P i = q ⁻¹ᵁ P i := by
  ext z
  change p z ∈ P i ↔ q z ∈ P i
  have hmem (j : Fin m) : p z ∈ U j ↔ q z ∈ U j :=
    Iff.of_eq (congrArg (fun W : D.Opens ↦ z ∈ W) (hi j))
  simp only [mem_piece, hmem]

variable (hcover : iSup U = ⊤) (v : ∀ i, coefficients p q (U i) (hi i))

/-- Restrict each original full coefficient to its selected disjoint piece. -/
def pieceCoefficient (i : Fin m) : coefficients p q (P i) (piece_invariant p q U hi hc i) :=
  restriction p q (U i) (P i) (hi i) (piece_invariant p q U hi hc i) (piece_le U hc i) (v i)

include hcover in
/-- The disjoint cover glues arbitrary full invariant coefficients uniquely on its pieces. -/
theorem existsUnique_selection :
    ∃! z : compatibleFunctions p q,
      ∀ i, (ιP i).appTop z.val = (X.homOfLE (piece_le U hc i)).appTop (v i).val := by
  apply existsUnique_invariant p q (fun i ↦ P i) (piece_invariant p q U hi hc)
    (by rw [iSup_piece, hcover]) (pieceCoefficient p q U hi hc v)
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · apply Subtype.ext
    exact section_eq_of_disjoint (P i) (P j) (piece_inf_eq_bot U hc h) _ _

/-- A full global invariant chosen from the fixed disjoint refinement. -/
def select : compatibleFunctions p q :=
  (existsUnique_selection p q U hi hc hcover v).choose

/-- Selection preserves the exact local value on its assigned piece. -/
theorem select_piece (i : Fin m) :
    (ιP i).appTop (select p q U hi hc hcover v).val =
      (X.homOfLE (piece_le U hc i)).appTop (v i).val :=
  (existsUnique_selection p q U hi hc hcover v).choose_spec.1 i

/-- Selection retains a common full boundary value; no reduced boundary is substituted. -/
theorem select_boundary (I : X.IdealSheafData) (t : Γ(I.subscheme, ⊤))
    (hb : ∀ i, (I.comap (U i).ι).subschemeι.appTop (v i).val =
      (map (I.comap (U i).ι) I (U i).ι rfl).appTop t) :
    I.subschemeι.appTop (select p q U hi hc hcover v).val = t := by
  apply OpenCoverFullBoundaryDetection.boundary_eq_of_local (fun i ↦ P i)
    (by rw [iSup_piece, hcover]) I
  intro i
  rw [select_piece]
  let g := X.homOfLE (piece_le U hc i)
  have he : (I.comap (U i).ι).comap g = I.comap (ιP i) := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
  rw [section_square _ _ g he, hb i]
  change (map (I.comap (ιP i)) (I.comap (U i).ι) g he ≫
    map (I.comap (U i).ι) I (U i).ι rfl).appTop t = _
  apply congrArg (fun f : (I.comap (ιP i)).subscheme ⟶ I.subscheme ↦ f.appTop t)
  apply (cancel_mono I.subschemeι).mp
  simp only [Category.assoc, map_inclusion, map_inclusion_assoc, g, Scheme.homOfLE_ι]

end FLT.Mazur.InvariantClopenCoverSelection
