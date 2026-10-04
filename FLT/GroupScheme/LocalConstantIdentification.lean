/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantGroupPoints
public import FLT.GroupScheme.LocalModelIdentification

/-!
# Constant identification of the original local model

A p-killed local model with trivial generic action is the explicit constant
integral model in small ramification. Integral étaleness is a consequence,
rather than a hypothesis, and the point comparison is prescribed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  (hX : ∀ x : X.Points, p • x = 0)
  (htriv : ∀ (g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) (x : X.Points), g • x = x)

include he hX htriv in
/-- The actual model is uniquely the explicit integral constant model on its points. -/
theorem existsUnique_local_constant_iso :
    ∃! e : X.Iso (constantGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) X.Points),
      ∀ x, genericHom e.toBialgHom x =
        constantGroupPoint (v.adicCompletionIntegers K) (v.adicCompletion K) X.Points x := by
  let f : GenericGaloisHom X
      (constantGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) X.Points) :=
    { toAddMonoidHom := (constantGroupPointEquiv _ _ _).toAddMonoidHom
      map_smul' g x := by
        rw [htriv, constantGroupModel_smul] }
  obtain ⟨e, he', hu⟩ := existsUnique_iso_of_local_killed v p he hX f
    (constantGroupPoint_bijective _ _ _)
  refine ⟨e, fun x ↦ DFunLike.congr_fun he' x, ?_⟩
  intro i hi
  exact hu i (by ext x; exact hi x)

include he hX htriv in
/-- Trivial generic action forces integral étaleness under the local ramification bound. -/
theorem local_etale_of_trivial : Algebra.Etale (v.adicCompletionIntegers K) X.CoordinateRing := by
  obtain ⟨e, -, -⟩ := existsUnique_local_constant_iso v p X he hX htriv
  let : Algebra.Etale (v.adicCompletionIntegers K)
      (constantGroupModel (v.adicCompletionIntegers K)
        (v.adicCompletion K) X.Points).CoordinateRing :=
    Algebra.Etale.of_equiv (constantGroupCoordinates _ _ _).symm
  exact Algebra.Etale.of_equiv e.toAlgEquiv

end ThreeAdicPlan
