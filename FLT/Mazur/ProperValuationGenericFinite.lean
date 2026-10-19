/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperSplitGenericFiniteness
public import FLT.Mazur.SurjectiveDominantEpi

/-!
# Generic finiteness on proper flat valuation models

Flatness makes the actual generic fiber schematically dense. Over a geometric
valuation ring, its finite set of points therefore forces integral finiteness.
The categorical comparison also retains generic finiteness under scalar change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.ProperValuationGenericFinite

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [Flat f]

omit [IsDomain R] [ValuationRing R] in
/-- The actual generic fiber of a flat valuation model is schematically dense. -/
theorem generic_dense :
    IsSchemeTheoreticallyDominant
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  let _ := SurjectiveDominantEpi.spec_schematic (algebraMap R K) (IsFractionRing.injective R K)
  infer_instance

/-- A proper flat model with finite geometric generic fiber is finite over the valuation ring. -/
theorem finite_geometric [IsAlgClosed K] [IsProper f]
    [IsFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsFinite f := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let _ := generic_dense (K := K) f
  exact ProperSplitGenericFiniteness.finite_of_geometric_dense f (pullback.fst f b)
    (pullback.fst f b).denseRange (pullback.snd f b) pullback.condition

variable {S T U V Y : Scheme} (a : Y ⟶ S) (g : T ⟶ S) (q : U ⟶ T)
  (b : V ⟶ S) (c : U ⟶ V) (h : q ≫ g = c ≫ b)

include h in
/-- The entire generic finite scheme is retained under a compatible integral scalar change. -/
theorem finite_generic_baseChange [IsFinite (pullback.snd a b)] :
    IsFinite (pullback.snd (pullback.snd a g) q) := by
  have outer := (IsPullback.of_hasPullback (pullback.snd a g) q).paste_horiz
    (IsPullback.of_hasPullback a g)
  rw [h] at outer
  have inner := outer.flip.of_bot' (IsPullback.of_hasPullback a b).flip
  exact MorphismProperty.of_isPullback inner.flip
    (inferInstanceAs (IsFinite (pullback.snd a b)))

/-- Finite fibers descend along any surjective change of the base. -/
theorem finite_fiber_of_surjective_baseChange [Surjective g]
    [IsFinite (pullback.snd a g)] (y : S) : (a ⁻¹' {y}).Finite := by
  obtain ⟨z, hz⟩ := g.surjective y
  apply ((pullback.snd a g).finite_preimage_singleton z).image (pullback.fst a g) |>.subset
  intro x hx
  obtain ⟨w, hwx, hwz⟩ := Scheme.Pullback.exists_preimage_pullback x z (hx.trans hz.symm)
  exact ⟨w, hwz, hwx⟩

/-- A proper map is finite when its whole pullback along a surjective base change is finite. -/
theorem finite_of_surjective_baseChange [IsProper a] [Surjective g]
    [IsFinite (pullback.snd a g)] : IsFinite a := by
  let _ : LocallyQuasiFinite a := LocallyQuasiFinite.of_finite_preimage_singleton a
    (finite_fiber_of_surjective_baseChange a g)
  exact IsFinite.of_isProper_of_locallyQuasiFinite a

end FLT.Mazur.ProperValuationGenericFinite
