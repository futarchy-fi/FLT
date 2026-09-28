/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtaleGenericMorphismExtension
public import FLT.GroupScheme.RaynaudSplitting

/-!
# Lifting generic splittings of étale models

Over an integrally closed base, a generic splitting lifts uniquely if the
middle and quotient models are étale. All three splitting identities hold
for the prescribed integral maps. This supplies the étale part of arithmetic
splitting descent once the away models have been shown to be étale.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField K]

/-- A generic splitting of étale middle and quotient models lifts uniquely to
a splitting of the prescribed integral maps over any integrally closed base. -/
theorem GenericSplitSequence.existsUnique_modelSplitting_of_etale
    {S X Q : FF R K} [Algebra.Etale R X.CoordinateRing] [Algebra.Etale R Q.CoordinateRing]
    (E : GenericSplitSequence S X Q) (i : ModelHom S X) (q : ModelHom X Q)
    (hi : genericHom i = E.inclusion) (hq : genericHom q = E.projection) :
    ∃! EO : ModelSplitting i q, EO.toGenericSplitSequence = E := by
  obtain ⟨r, hr, _⟩ := extend_generic_morphism_of_etale X S E.retraction
  obtain ⟨s, hs, _⟩ := extend_generic_morphism_of_etale Q X E.sectionMap
  have hir : i.comp r = BialgHom.id R S.CoordinateRing := by
    apply genericHom_injective S S
    ext x
    simpa only [genericHom_comp, genericHom_id, hr, hi] using E.retract x
  have hsq : s.comp q = BialgHom.id R Q.CoordinateRing := by
    apply genericHom_injective Q Q
    ext x
    simpa only [genericHom_comp, genericHom_id, hs, hq] using E.sectionProjection x
  have hd : ModelHom.add (r.comp i) (q.comp s) = BialgHom.id R X.CoordinateRing := by
    apply genericHom_injective X X
    ext x
    simpa only [ModelHom.genericHom_add, genericHom_comp, genericHom_id, hr, hs, hi, hq]
      using E.decomposition x
  let EO : ModelSplitting i q := ⟨r, s, hir, hsq, hd⟩
  have hEO : EO.toGenericSplitSequence = E := by
    cases E
    simp only [ModelSplitting.toGenericSplitSequence, EO] at *
    cases hi
    cases hq
    cases hr
    cases hs
    rfl
  exact ⟨EO, hEO, fun F hF ↦
    ModelSplitting.toGenericSplitSequence_injective (hF.trans hEO.symm)⟩

end ThreeAdicPlan
