/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactEtaleGeometricSections
public import FLT.Mazur.SectionProperNeighborhood

/-!
# One finite open containing the entire distinguished etale fiber

For a separated quasi-compact etale morphism, construct a common affine etale
ground and a single clopen finite etale neighborhood of its whole distinguished
fiber. The original geometric test factors exactly through that ground.
The complementary open has empty distinguished fiber, but can have points
over other ground points; no global coverage of this remainder is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleWholeFiberProperNeighborhood
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [QuasiCompact f] [IsSeparated f]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

omit [Etale f] [QuasiCompact f] in
/-- A proper open over a separated target is closed in the original source. -/
theorem isClosed_of_proper_open (T : X.Opens) [IsProper (T.ι ≫ f)] :
    IsClosed (T : Set X) := by
  let _ := IsProper.of_comp T.ι f
  simpa only [Scheme.Opens.range_ι] using T.ι.isClosedMap.isClosed_range

/-- Construct a finite clopen chart containing every point of the distinguished changed fiber. -/
theorem exists_finite_open :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U),
      IsAffine U ∧ Etale q ∧ z ≫ q = b ∧
      ∃ T : (pullback f q).Opens,
        IsClosed (T : Set (pullback f q : Scheme.{u})) ∧
        IsFinite (T.ι ≫ pullback.snd f q) ∧ Etale (T.ι ≫ pullback.snd f q) ∧
        IsAffine T.toScheme ∧ T ≤ ProperNeighborhoodAtlas.locus (pullback.snd f q) ∧
        ∀ x : (pullback f q : Scheme.{u}), pullback.snd f q x = z default → x ∈ T := by
  obtain ⟨n, U, q, z, s, hU, hq, hz, hs, _, hc⟩ :=
    QuasiCompactEtaleGeometricSections.exists_affine_sections f b
  let _ := hU
  obtain ⟨T, hf, he, hT, ht⟩ :=
    SectionProperNeighborhood.exists_finite_open (pullback.snd f q) s hs
  let _ := hf
  exact ⟨U, q, z, hU, hq, hz, T, isClosed_of_proper_open (pullback.snd f q) T,
    hf, he, isAffine_of_isAffineHom (T.ι ≫ pullback.snd f q), hT,
    fun x hx ↦ (ht x).mpr (by simpa only [hx] using hc x hx)⟩

/-- The constructed proper-neighborhood locus covers the entire distinguished ambient fiber. -/
theorem exists_ground_fiber_in_locus :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U),
      IsAffine U ∧ Etale q ∧ z ≫ q = b ∧
      ∀ x : (pullback f q : Scheme.{u}), pullback.snd f q x = z default →
        x ∈ ProperNeighborhoodAtlas.locus (pullback.snd f q) := by
  obtain ⟨U, q, z, hU, hq, hz, T, _, _, _, _, hT, ht⟩ := exists_finite_open f b
  exact ⟨U, q, z, hU, hq, hz, fun x hx ↦ hT (ht x hx)⟩

end FLT.Mazur.EtaleWholeFiberProperNeighborhood
