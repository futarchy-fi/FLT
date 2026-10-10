/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSmoothGenericFiberOpen
public import Mathlib.Topology.Constructible

/-!
# Constructible connected-fiber pieces on reduced integral closed strata

For each prime ideal, the actual family over its domain quotient has a generic
open comparison. Its image is a constructible piece on the original closed stratum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace
namespace FLT.Mazur.Approximation
open SchemeProperGeometricFiberSections

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Smooth f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs in
/-- Every reduced integral closed stratum has a nonempty constructible generic piece. -/
theorem exists_connectedFiber_primeStratum_piece (p : Ideal R) [p.IsPrime] :
    ∃ U : Set (Spec R), IsOpen U ∧
      (PrimeSpectrum.zeroLocus p ∩ U).Nonempty ∧
        IsConstructible (geometricallyConnectedLocus f ∩ PrimeSpectrum.zeroLocus p ∩ U) := by
  let Q : CommRingCat := .of (R ⧸ p)
  let j : Spec Q ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
  let g := pullback.snd f j
  let t := baseChangedSection f s hs j
  obtain ⟨a, ha, hopen⟩ := exists_generic_isOpen_connectedFiber g t
    (baseChangedSection_projection f s hs j)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  have hnr : r ∉ p := fun h ↦ ha (hr.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  have hrange : Set.range j = PrimeSpectrum.zeroLocus (p : Set R) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
  have hpre : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Q)) =
      j ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    rw [← hr]
    rfl
  have hcon := (NoetherianSpace.isCompact _).isConstructible hopen
  have him := hcon.image_of_isClosedEmbedding j.isClosedEmbedding
    (fun _ _ _ ↦ NoetherianSpace.isCompact _)
  have heq : j '' (geometricallyConnectedLocus g ∩
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Q))) =
      geometricallyConnectedLocus f ∩ PrimeSpectrum.zeroLocus p ∩
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    rw [geometricallyConnectedLocus_of_isPullback (IsPullback.of_hasPullback f j),
      hpre, ← Set.preimage_inter, Set.image_preimage_eq_inter_range, hrange]
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  refine ⟨(PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)),
    (PrimeSpectrum.basicOpen r).isOpen, ?_, heq ▸ him⟩
  exact ⟨⟨p, inferInstance⟩, (fun _ h ↦ h), hnr⟩

end FLT.Mazur.Approximation
