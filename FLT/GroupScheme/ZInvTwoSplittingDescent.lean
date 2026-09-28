/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ZInvTwoGenericMorphismExtension
public import FLT.GroupScheme.RaynaudSplitting

/-!
# Descent of prescribed generic splittings over `ℤ[1/2]`

The away étaleness and local filtration hypotheses concern the actual scalar
extensions of the original models. The theorem constructs the two integral
splitting maps, proves all three identities, and recovers the given rational
splitting. No compatible local maps or integral section are assumed.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan


open scoped TensorProduct
open PadicPatching

local instance zInvTwoSplittingDescentInst1 : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

/-- A rational splitting descends to the specified integral maps when the
middle and quotient models are étale away from three and filtered locally. -/
theorem GenericSplitSequence.existsUnique_modelSplitting_over_zInvTwo
    {S X Q : FF ZInvTwo ℚ}
    [Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] X.CoordinateRing)]
    [Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] Q.CoordinateRing)]
    {m n : ℕ}
    (hX : (X.scalarExtension ℤ_[3] ℚ_[3]).HasOrderThreeFiltration m)
    (hQ : (Q.scalarExtension ℤ_[3] ℚ_[3]).HasOrderThreeFiltration n)
    (E : GenericSplitSequence S X Q) (i : ModelHom S X) (q : ModelHom X Q)
    (hi : genericHom i = E.inclusion) (hq : genericHom q = E.projection) :
    ∃! EO : ModelSplitting i q, EO.toGenericSplitSequence = E := by
  obtain ⟨r, hr, _⟩ := extend_generic_morphism_over_zInvTwo X S hX E.retraction
  obtain ⟨s, hs, _⟩ := extend_generic_morphism_over_zInvTwo Q X hQ E.sectionMap
  have hir : i.comp r = BialgHom.id ZInvTwo S.CoordinateRing := by
    apply genericHom_injective S S
    ext x
    simpa only [genericHom_comp, genericHom_id, hr, hi] using E.retract x
  have hsq : s.comp q = BialgHom.id ZInvTwo Q.CoordinateRing := by
    apply genericHom_injective Q Q
    ext x
    simpa only [genericHom_comp, genericHom_id, hs, hq] using E.sectionProjection x
  have hd : ModelHom.add (r.comp i) (q.comp s) = BialgHom.id ZInvTwo X.CoordinateRing := by
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
