/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialEnvelopeFullFiber
public import FLT.Mazur.JointTranslationNormSupport

/-!
# Norm support using only charts of the bad locus

The finite norm product still detects the full ambient fiber when the chosen
translation charts cover only the translation coordinates of the zero locus.
Compactness selects such a finite family from any open family covering those
coordinates; it need not cover the whole ambient translation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type} (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- The partial charts carry their actual structural algebras. -/
local instance partialTranslationAlgebra (i : I) : Algebra R Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) R Γ((T i).left, ⊤))
  (s : Γ((prod B W).left, ⊤))
local notation "U" => Scheme.basicOpen (Over.left (prod B W)) s
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "ρ" => Over.Hom.left (prod.snd : prod B W ⟶ W)
variable (ht : ∀ y : (prod B W).left, y ∉ (prod B W).left.basicOpen s →
  ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)

include ht b

/-- Covering the zero locus is sufficient for the actual norm product to test every fiber. -/
theorem basicOpen_partialTranslationNorm_fullFiber [Fintype I] :
    (B.left.basicOpen (jointTranslationNorm B W T t b s) : Set B.left) =
      fullFiberLocus π U := by
  rw [fullFiberLocus_partialTranslationCover B W T t U ht]
  ext x
  simp only [Set.mem_iInter]
  exact mem_basicOpen_jointTranslationNorm_iff B W T t b s x

/-- Finite free charts covering only bad coordinates already prove ambient fullness is open. -/
theorem isOpen_fullFiber_of_partialTranslationCover [Finite I] :
    IsOpen (fullFiberLocus π U) := by
  let _ := Fintype.ofFinite I
  rw [← basicOpen_partialTranslationNorm_fullFiber B W T t b s ht]
  exact (B.left.basicOpen _).isOpen

omit b [∀ i, IsAffine (T i).left] in
/-- A compact zero locus selects finitely many translation charts from an open partial cover. -/
theorem exists_finite_partialTranslationCover
    (hU : IsCompact (U : Set (prod B W).left)ᶜ)
    (ho : ∀ i, IsOpen (Set.range (t i).left)) :
    ∃ J : Finset I, ∀ y : (prod B W).left, y ∉ U →
      ∃ i ∈ J, ∃ z : (T i).left, (t i).left z = (ρ) y := by
  have hc := hU.image (ρ).continuous
  obtain ⟨J, hJ⟩ := hc.elim_finite_subcover (fun i ↦ Set.range (t i).left) ho (by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i, z, hz⟩ := ht y hy
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩)
  refine ⟨J, fun y hy ↦ ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ ⟨y, hy, rfl⟩)
  obtain ⟨hiJ, z, hz⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hiJ, z, hz⟩

/-- Compactness and an arbitrary open partial family construct a genuine source coefficient. -/
theorem exists_partialTranslationNorm
    (hU : IsCompact (U : Set (prod B W).left)ᶜ)
    (ho : ∀ i, IsOpen (Set.range (t i).left)) :
    ∃ r : Γ(B.left, ⊤), (B.left.basicOpen r : Set B.left) = fullFiberLocus π U := by
  classical
  obtain ⟨J, hJ⟩ := exists_finite_partialTranslationCover B W T t s ht hU ho
  let TJ : J → Over (Spec (.of R)) := fun i ↦ T i.val
  let tJ : ∀ i, TJ i ⟶ W := fun i ↦ t i.val
  let bJ := fun i : J ↦ b i.val
  refine ⟨jointTranslationNorm B W TJ tJ bJ s, ?_⟩
  apply basicOpen_partialTranslationNorm_fullFiber B W TJ tJ bJ s
  intro y hy
  obtain ⟨i, hi, z, hz⟩ := hJ y hy
  exact ⟨⟨i, hi⟩, z, hz⟩

/-- The arbitrary partial cover gives openness after finite subcover extraction. -/
theorem isOpen_fullFiber_of_compact_partialTranslationCover
    (hU : IsCompact (U : Set (prod B W).left)ᶜ)
    (ho : ∀ i, IsOpen (Set.range (t i).left)) : IsOpen (fullFiberLocus π U) := by
  obtain ⟨r, hr⟩ := exists_partialTranslationNorm B W T t b s ht hU ho
  rw [← hr]
  exact (B.left.basicOpen r).isOpen

end FLT.Mazur.SchemeTranslationNorm
