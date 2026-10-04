/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Lifting covers with a monic one-equation presentation

This constructs a flat cover only for the stated presentation. It does not assert
that an arbitrary division cover has such a presentation.
-/

@[expose] public noncomputable section
open Polynomial
namespace AdjoinRoot
variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- A monic root cover lifts through a surjection, preserving degree and its root. -/
theorem exists_monic_cover_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (f : C[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ g : B[X], g.Monic ∧ g.map q.toRingHom = f ∧
      g.natDegree = f.natDegree ∧ Module.Finite B (AdjoinRoot g) ∧
      Module.Free B (AdjoinRoot g) ∧ Module.FaithfullyFlat B (AdjoinRoot g) ∧
      ∃ t : AdjoinRoot g →ₐ[R] AdjoinRoot f,
        t (root g) = root f ∧ ∀ b, t (of g b) = of f (q b) := by
  obtain ⟨g, hgf, hd, hg⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := q.toRingHom) (f.lifts_iff_coeff_lifts.mpr fun n ↦ hq (f.coeff n)) hf
  have hpos : 0 < g.natDegree := hd.symm ▸ hdeg
  let : Module.Free B (AdjoinRoot g) := hg.free_adjoinRoot
  have hfaith : Module.FaithfullyFlat B (AdjoinRoot g) := by
    let : Nonempty (Fin (powerBasis' hg).dim) := ⟨⟨0, hpos⟩⟩
    exact Module.FaithfullyFlat.of_linearEquiv B _ (powerBasis' hg).basis.repr
  refine ⟨g, hg, hgf, hd, hg.finite_adjoinRoot, inferInstance, hfaith, ?_⟩
  refine ⟨mapAlgHom q g f (hgf ▸ dvd_refl f), ?_, ?_⟩
  · simp [coe_mapAlgHom]
  · intro b
    simp [coe_mapAlgHom]

end AdjoinRoot
