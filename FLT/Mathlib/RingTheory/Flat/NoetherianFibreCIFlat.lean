/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.NoetherianRelativeCIFlat
public import FLT.Mathlib.RingTheory.Flat.FibreRegularityAtStalk

/-! # Fibrewise complete intersections in a Noetherian flat algebra are flat -/

@[expose] public noncomputable section

open Algebra.TensorProduct RingTheory.Sequence

namespace Module.Flat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing S] [Flat R S]

/-- Fibrewise regular equations in a Noetherian flat ambient algebra give a
flat quotient. The hypothesis concerns only fibre points on the zero locus. -/
theorem flat_quotient_of_fibre_regular (rs : List S)
    (hrs : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime],
      Ideal.ofList (rs.map (includeRight : S →ₐ[R] p.Fiber S)) ≤ q →
      IsWeaklyRegular (Localization.AtPrime q)
        ((rs.map (includeRight : S →ₐ[R] p.Fiber S)).map
          (algebraMap _ (Localization.AtPrime q)))) :
    Flat R (S ⧸ Ideal.ofList rs) := by
  apply flat_quotient_of_local_fibre_sequence
  intro P _ hP
  obtain ⟨q, hqprime, hq⟩ := Ideal.exists_residue_fibre_prime (R := R) P
  let : q.IsPrime := hqprime
  apply Ideal.weaklyRegular_stalkFibre_of_fibre P rs q hq
  apply hrs
  change Ideal.ofList (rs.map (includeRight :
    S →ₐ[R] (P.comap (algebraMap R S)).Fiber S).toRingHom) ≤ q
  rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap]
  exact hP.trans hq.symm.le

end Module.Flat
