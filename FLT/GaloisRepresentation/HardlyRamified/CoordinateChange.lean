/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# Coordinate changes for hardly ramified representations

Linear equivalences preserve all four conditions, including when the source
and target coefficient modules belong to different universes.
-/

@[expose] public noncomputable section

open scoped TensorProduct NumberField

namespace GaloisRep

set_option backward.isDefEq.respectTransparency false in
/-- Flatness is preserved by a linear equivalence between arbitrary module universes. -/
theorem IsFlatAt.conj {R V W : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
    (ρ : GaloisRep ℚ R V) (e : V ≃ₗ[R] W)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hρ : ρ.IsFlatAt v) : (ρ.conj e).IsFlatAt v := by
  constructor
  intro I hI
  let σ := (ρ.baseChange (R ⧸ I)).toLocal v
  let τ := ((ρ.conj e).baseChange (R ⧸ I)).toLocal v
  let eI := e.baseChange R (R ⧸ I) V W
  let f : σ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] τ.Space :=
    { eI.toAddMonoidHom with
      map_smul' := by
        intro g x
        change eI (σ g x) = τ g (eI x)
        induction x using TensorProduct.inductionOn with
        | tmul r x =>
          change r ⊗ₜ[R] e (ρ.toLocal v g x) =
            r ⊗ₜ[R] e (ρ.toLocal v g (e.symm (e x)))
          rw [e.symm_apply_apply]
        | add x y hx hy => simp_all }
  exact (hρ.cond I hI).map _ _ _ _ f eI.bijective

end GaloisRep

namespace GaloisRepresentation.IsHardlyRamified

/-- Every hardly ramified condition survives a linear change of coordinates. -/
theorem conj {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {R V W : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
    (hV : Module.rank R V = 2) (hW : Module.rank R W = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hp hV ρ) (e : V ≃ₗ[R] W) :
    IsHardlyRamified hp hW (ρ.conj e) := by
  refine ⟨?_, ?_, hρ.isFlat.conj ρ e _, ?_⟩
  · intro g
    change (e.conj (ρ g)).det = _
    exact (LinearMap.det_conj (ρ g) e).trans (hρ.det g)
  · intro q hq hgood
    have instUnramified := hρ.isUnramified q hq hgood
    infer_instance
  · obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
    refine ⟨π.comp e.symm.toLinearMap, hπ.comp e.symm.surjective, δ, ?_⟩
    intro g x
    simpa [GaloisRep.map_conj, GaloisRep.conj_apply_apply] using hδ g (e.symm x)

end GaloisRepresentation.IsHardlyRamified
