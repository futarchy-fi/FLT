/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiberEvaluationLocus
public import FLT.Mazur.NoetherianInfinitesimalFiberFunctions

/-!
# Connectedness on infinitesimal neighborhoods of one closed fiber

Every point of a maximal-ideal-power quotient maps to the chosen closed point.
The actual geometric connectedness locus therefore proves connectedness on
all these infinitesimal base changes using only the original closed fiber.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Every point of a maximal-ideal-power quotient lies over the same closed point. -/
theorem quotient_pow_specMap_apply {R : CommRingCat} (J : Ideal R) [J.IsMaximal]
    (n : ℕ) (p : Spec (.of (R ⧸ J ^ n))) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))) p =
      (⟨J, inferInstance⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change p.asIdeal.comap (Ideal.Quotient.mk (J ^ n)) = J
  have hle : J ^ n ≤ p.asIdeal.comap (Ideal.Quotient.mk (J ^ n)) := by
    simpa only [Ideal.mk_ker] using
      (Ideal.ker_le_comap (Ideal.Quotient.mk (J ^ n)) :
        RingHom.ker _ ≤ p.asIdeal.comap (Ideal.Quotient.mk (J ^ n)))
  exact (Ideal.IsMaximal.eq_of_le ‹J.IsMaximal›
    (Ideal.IsPrime.ne_top') (Ideal.IsPrime.le_of_pow_le hle)).symm

/-- A connected geometric closed fiber controls every infinitesimal thickening of that point. -/
theorem geometricallyConnected_quotient_pow {R : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec R) (J : Ideal R) [J.IsMaximal] (n : ℕ)
    (hc : (⟨J, inferInstance⟩ : PrimeSpectrum R) ∈ geometricallyConnectedLocus f) :
    GeometricallyConnected
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))) := by
  apply (geometricallyConnectedLocus_eq_univ_iff _).mp
  rw [geometricallyConnectedLocus_of_isPullback (IsPullback.of_hasPullback _ _)]
  apply Set.eq_univ_iff_forall.mpr
  intro p
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))) p ∈ geometricallyConnectedLocus f
  rwa [quotient_pow_specMap_apply]

/-- A pointed proper reduced closed fiber is enough to supply the geometric hypothesis. -/
theorem mem_locus_of_connected_reduced_fiber {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (b : S) [ConnectedSpace (f.fiber b)] [IsReduced (f.fiber b)] :
    b ∈ geometricallyConnectedLocus f := by
  have : IsProper (f.fiberToSpecResidueField b) :=
    inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField b)))
  exact geometricallyConnected_of_proper_connected_reduced_section
    (f.fiberToSpecResidueField b) (residueFiberSection f s hs b)
    (residueFiberSection_projection f s hs b)

end FLT.Mazur.Approximation
