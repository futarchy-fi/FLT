/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicIndependentFppfImage
public import FLT.Mazur.EtaleCyclicSmoothLocusIndependentCoverage
public import FLT.Mazur.IndependentCyclicNormalizedModuli

/-!
# Independent normalized coverage at every positive cyclic order

The actual independent closed slice represents the original classes on a
proved fppf cover. It covers the smooth locus even when the original family
has singular fibers elsewhere. The earlier coprimality restriction is removed;
local noetherianness, an etale subgroup, and invertibility of two remain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  (hc : H.IsCyclic) (ha : H.IsAmple) (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂

/-- Every original smooth-locus point admits an actual independent normalized representative. -/
theorem exists_smoothLocus_independent_normalized_neighborhood {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ independentCyclicNormalizedSlice n,
          (independentCyclicNormalizedModuliMap n).app (Opposite.op U) (ULift.up p) =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨U, g, hg, hl, hxg, hV, p, hp⟩ :=
    exists_smoothLocus_independent_neighborhood H hc ha h₂ hx hxV
  exact ⟨U, g, hg, hl, hxg, hV, independentCyclicNormalizedSlicePoint n p,
    (independentCyclicNormalizedModuliMap_normalization n p).trans hp⟩

variable [Smooth E.curve.hom]

/-- A small fppf family of independent normalized points represents the actual original object. -/
theorem exists_independent_normalized_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ independentCyclicNormalizedSlice n),
      ∀ i, (independentCyclicNormalizedModuliMap n).app (Opposite.op (C.X i)) (ULift.up (p i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, p, hp⟩ := exists_independent_fppf_cover H hc ha h₂
  exact ⟨C, fun i ↦ independentCyclicNormalizedSlicePoint n (p i),
    fun i ↦ (independentCyclicNormalizedModuliMap_normalization n (p i)).trans (hp i)⟩

/-- The independent closed slice's image sieve covers every original class in this sector. -/
theorem independent_normalized_imageSieve_mem :
    Presheaf.imageSieve (independentCyclicNormalizedModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := exists_independent_normalized_fppf_cover H hc ha h₂
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

/-- Independent normalized image coverage survives every further test-scheme base change. -/
theorem independent_normalized_pullback_imageSieve_mem {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (independentCyclicNormalizedModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g
    (independent_normalized_imageSieve_mem H hc ha h₂)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
