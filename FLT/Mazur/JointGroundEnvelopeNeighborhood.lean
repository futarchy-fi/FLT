/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointGroundNormInterior
public import FLT.Mazur.AffineHilbertEnvelopeFiberCount

/-!
# Original envelope neighborhoods from finite translation subcharts

Prime avoidance constructs original envelope coefficients around entire fibers.
Joint changed-ground norm domains then prove that the full-fiber locus of ANY
open is open. No original finite basis or extension of a chosen section is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  [IsAffine V.left] [Etale V.hom]
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  {A : Over (Spec (.of R))} [IsAffine A.left] {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  (hsurj : Function.Surjective u.left)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Each finite translation chart carries its actual structural algebra. -/
local instance jointNeighborhoodTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ z : W.left, ∃ i, ∃ y : (T i).left, (t i).left y = z)
  (U : (prod A V).left.Opens)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- An actual original coefficient keeps the entire finite fiber inside the requested open. -/
theorem exists_originalEnvelope_fiber_coefficient (x : A.left)
    (hx : x ∈ fullFiberLocus π U) :
    ∃ s : Γ((prod A V).left, ⊤),
      x ∈ fullFiberLocus π ((prod A V).left.basicOpen s) ∧
        (prod A V).left.basicOpen s ≤ U := by
  let _ : IsAffine (prod A V).left := IsAffine.of_isIso (Over.prodLeftIsoPullback A V).hom
  obtain ⟨s, hs, hsU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal U
    (π ⁻¹' {x}) (independentEnvelope_finite_fiber V x)
    (fun y hy ↦ (mem_fullFiberLocus π U x).mp hx y hy)
  exact ⟨s, (mem_fullFiberLocus π _ x).mpr (fun y hy ↦ hs hy), hsU⟩

include H hu hsurj b ht

/-- Finite changed-ground charts supply open neighborhoods for every original full-fiber point. -/
theorem isOpen_originalFullFiber_open_of_jointGroundCover : IsOpen (fullFiberLocus π U) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨s, hs, hsU⟩ := exists_originalEnvelope_fiber_coefficient V U x hx
  refine ⟨fullFiberLocus π ((prod A V).left.basicOpen s), ?_, ?_, hs⟩
  · intro y hy
    apply (mem_fullFiberLocus π U y).mpr
    intro z hz
    exact hsU ((mem_fullFiberLocus π _ y).mp hy z hz)
  · exact isOpen_originalFullFiber_of_jointGroundCover a V W w H u T t b ht s hu hsurj

/-- The original maximal open retains every full-fiber point of the arbitrary envelope open. -/
theorem originalFullInterior_open_eq_fullFiber :
    (fullFiberInterior π U : Set A.left) = fullFiberLocus π U :=
  (isOpen_originalFullFiber_open_of_jointGroundCover a V W w H u hu hsurj T t b ht U).interior_eq

/-- Every finite set of retained original points has a single genuine source denominator. -/
theorem exists_originalFullFiber_source_coefficient (F : Set A.left) (hF : F.Finite)
    (hFU : F ⊆ fullFiberLocus π U) :
    ∃ r : Γ(A.left, ⊤), F ⊆ A.left.basicOpen r ∧
      r ∈ denominatorIdeal (π).appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  rwa [originalFullInterior_open_eq_fullFiber a V W w H u hu hsurj T t b ht U]

end FLT.Mazur.SchemeTranslationNorm
