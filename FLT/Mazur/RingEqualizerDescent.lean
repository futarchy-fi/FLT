/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchematicDescentGluing
public import FLT.Mazur.RingEqualizerAwayEndpoint
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# Global descent from local endpoint neighborhoods

Finite equalizer normalizations descend uniquely once local descent is known
at every endpoint-base prime. Outside that image the normalization is already
an isomorphism. The resulting neighborhoods cover the entire spectrum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.RingEqualizerDescent
open RingEqualizerLocalDescent RingEqualizerLocalization
variable {C D : Type u} [CommRing C] [CommRing D] (f g : C →+* D)

/-- Descent near each endpoint-base prime gives global unique descent. -/
theorem exists_desc {Y : Scheme.{u}} (h : Spec (.of C) ⟶ Y)
    (hf : (f.eqLocus g).subtype.Finite)
    (he : Function.Surjective (f.comp (f.eqLocus g).subtype))
    (hl : ∀ x : PrimeSpectrum D,
      ∃ (s : f.eqLocus g) (d : Spec (.of (E f g s)) ⟶ Y), f s.val ∉ x.asIdeal ∧
        branch f g s ≫ d = branchOpen f g s ≫ h) :
    ∃! d : Spec (.of (f.eqLocus g)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (f.eqLocus g).subtype) ≫ d = h := by
  let π := Spec.map (CommRingCat.ofHom (f.eqLocus g).subtype)
  let : IsFinite π := by
    rw [IsFinite.SpecMap_iff]
    exact hf
  let : Surjective π := ⟨hf.to_isIntegral.comap_surjective Subtype.val_injective⟩
  let : IsSchemeTheoreticallyDominant π :=
    SurjectiveDominantEpi.spec_schematic _ Subtype.val_injective
  have H (z : PrimeSpectrum (f.eqLocus g)) :
      ∃ (s : f.eqLocus g) (d : Spec (.of (E f g s)) ⟶ Y), s ∉ z.asIdeal ∧
        branch f g s ≫ d = branchOpen f g s ≫ h := by
    by_cases hz : z ∈ Set.range (PrimeSpectrum.comap (f.comp (f.eqLocus g).subtype))
    · obtain ⟨x, rfl⟩ := hz
      exact hl x
    · rw [range_comap_of_surjective _ _ he] at hz
      obtain ⟨s, hs, hsz⟩ := Set.not_subset.mp hz
      obtain ⟨d, hd⟩ := RingEqualizerAwayEndpoint.exists_desc f g s h hs
      exact ⟨s, d, hsz, hd⟩
  choose s d hs hd using H
  let 𝒰 : (Spec (.of (f.eqLocus g))).OpenCover := {
    I₀ := PrimeSpectrum (f.eqLocus g)
    X z := Spec (.of (E f g (s z)))
    f z := neighborhood f g (s z)
    mem₀ := by
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, fun _ ↦ inferInstance⟩
      intro z
      have hz : z ∈ Set.range (neighborhood f g (s z)) := by
        rw [range_neighborhood]
        exact hs z
      obtain ⟨t, ht⟩ := hz
      exact ⟨z, t, ht⟩ }
  apply SchematicDescentGluing.exists_desc_of_cover π h 𝒰 d
  intro z
  let sq := RingEqualizerLocalDescent.isPullback f g (s z)
  apply (cancel_epi sq.isoPullback.hom).mp
  simpa only [sq, π, 𝒰, ← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd] using (hd z).symm
end FLT.Mazur.RingEqualizerDescent
