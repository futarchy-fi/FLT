/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPuncture
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The image of the complete standard initial puncture

The constructed restriction from D(p) to D(q+a₁) has exactly the expected
p-principal image. It retains the original localization maps on both sides.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "L" => PolynomialNodeOpen W s
local notation "P" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (initialNodeStandardPuncture W s I hI ha hs)))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap N L))
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap N D))

/-- The full standard puncture restriction commutes with the actual node inclusions. -/
@[reassoc] theorem initialNodeStandardPuncture_spec_base : P ≫ b = i := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (initialNodeStandardPuncture_base W s I hI ha hs)

/-- The complete standard puncture restriction is an open immersion. -/
theorem initialNodeStandardPuncture_spec_isOpenImmersion : IsOpenImmersion P := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization (NodalFiber.p s)
  have hc : IsOpenImmersion (P ≫ b) := by
    rw [initialNodeStandardPuncture_spec_base]
    infer_instance
  exact IsOpenImmersion.of_comp P b

/-- The full standard puncture is exactly D(p) inside the original initial node neighborhood. -/
theorem initialNodeStandardPuncture_spec_range :
    Set.range P = (PrimeSpectrum.basicOpen (algebraMap N L (NodalFiber.p s)) :
      Set (PrimeSpectrum L)) := by
  let _ : IsOpenImmersion b :=
    IsOpenImmersion.of_isLocalization (NodalFiber.q s + algebraMap R N W.a₁)
  have hc := initialNodeStandardPuncture_spec_base W s I hI ha hs
  have hi := PrimeSpectrum.localization_away_comap_range D (NodalFiber.p s)
  have hb : Set.range P = b ⁻¹' Set.range i := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, (congrArg (fun f => f w) hc).symm⟩
    · rintro ⟨w, hw⟩
      refine ⟨w, (b).isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun f => f w) hc).trans hw
  rw [hb]
  change (PrimeSpectrum.comap (algebraMap N L)) ⁻¹'
    Set.range (PrimeSpectrum.comap (algebraMap N D)) = _
  rw [hi]
  rfl

/-- The puncture restriction is the complete pullback of D(p) along the full node open. -/
theorem initialNodeStandardPuncture_spec_isPullback : IsPullback (𝟙 _) P i b := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization (NodalFiber.p s)
  let _ := initialNodeStandardPuncture_spec_isOpenImmersion W s I hI ha hs
  apply IsOpenImmersion.isPullback
  · simpa only [Category.id_comp] using
      (initialNodeStandardPuncture_spec_base W s I hI ha hs)
  · apply TopologicalSpace.Opens.ext
    change b ⁻¹' Set.range i = Set.range P
    rw [initialNodeStandardPuncture_spec_range]
    change (PrimeSpectrum.comap (algebraMap N L)) ⁻¹'
      Set.range (PrimeSpectrum.comap (algebraMap N D)) = _
    rw [PrimeSpectrum.localization_away_comap_range D (NodalFiber.p s)]
    rfl

end FLT.Mazur.WeierstrassModificationX
