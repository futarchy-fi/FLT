/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialFiniteTranslationInterior

/-!
# Finite extraction from arbitrary partial translation families

Compactness of the excluded envelope selects finitely many translation charts
from any open family covering its translation coordinates. Affine independent
envelopes supply that compactness for every prescribed open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type} (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  (U : (prod B W).left.Opens)
  (ht : ∀ y : (prod B W).left, y ∉ U →
    ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
  (ho : ∀ i, IsOpen (Set.range (t i).left))
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "ρ" => Over.Hom.left (prod.snd : prod B W ⟶ W)

include ht ho

/-- Only the compact excluded locus, rather than the whole translation, needs a finite cover. -/
theorem exists_finite_partialTranslationCover_open
    (hU : IsCompact (U : Set (prod B W).left)ᶜ) :
    ∃ J : Finset I, ∀ y : (prod B W).left, y ∉ U →
      ∃ i ∈ J, ∃ z : (T i).left, (t i).left z = (ρ) y := by
  obtain ⟨J, hJ⟩ := (hU.image (ρ).continuous).elim_finite_subcover
    (fun i ↦ Set.range (t i).left) ho (by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨i, z, hz⟩ := ht y hy
      exact Set.mem_iUnion.mpr ⟨i, z, hz⟩)
  refine ⟨J, fun y hy ↦ ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ ⟨y, hy, rfl⟩)
  obtain ⟨hiJ, z, hz⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hiJ, z, hz⟩

variable [∀ i, IsAffine (T i).left]
/-- The selected charts keep their original structural algebras and bases. -/
local instance partialCompactTranslationAlgebra (i : I) : Algebra R Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) R Γ((T i).left, ⊤))

include b

/-- Finite extraction supplies the full-interior neighborhood for any prescribed envelope open. -/
theorem isOpen_fullFiber_open_of_compact_partialTranslation
    (hU : IsCompact (U : Set (prod B W).left)ᶜ) : IsOpen (fullFiberLocus π U) := by
  obtain ⟨J, hJ⟩ := exists_finite_partialTranslationCover_open B W T t U ht ho hU
  apply isOpen_fullFiber_open_of_partialFiniteTranslation B W (fun i : J ↦ T i.val)
    (fun i ↦ t i.val) (fun i ↦ b i.val) U
  intro y hy
  obtain ⟨i, hi, z, hz⟩ := hJ y hy
  exact ⟨⟨i, hi⟩, z, hz⟩

/-- Affineness supplies compactness without a noetherian or finite-type hypothesis. -/
theorem isOpen_fullFiber_open_of_affine_partialTranslation [IsAffine B.left] [IsAffine W.left] :
    IsOpen (fullFiberLocus π U) := by
  let _ : IsAffine (prod B W).left := IsAffine.of_isIso (Over.prodLeftIsoPullback B W).hom
  exact isOpen_fullFiber_open_of_compact_partialTranslation B W T t U ht ho b
    U.isOpen.isClosed_compl.isCompact

/-- These affine full-fiber points lie in the actual maximal original source open. -/
theorem fullInterior_eq_of_affine_partialTranslation [IsAffine B.left] [IsAffine W.left] :
    (fullFiberInterior π U : Set B.left) = fullFiberLocus π U :=
  (isOpen_fullFiber_open_of_affine_partialTranslation B W T t U ht ho b).interior_eq

end FLT.Mazur.SchemeTranslationNorm
