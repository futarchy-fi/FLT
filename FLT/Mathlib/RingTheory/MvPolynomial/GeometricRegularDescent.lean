/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.GeometricPointLocalization
public import FLT.Mathlib.RingTheory.LocalRing.IdealGeneratorDescent
public import FLT.GroupScheme.PolynomialLocalParameterCriterion

/-! # Descending regular relations at non-rational residue points -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ} (a : Fin n → K)

/-- A square Artinian geometric ideal supplies regular relations in the original local ring.
The point over the original field is its contraction, with no rational-residue assumption. -/
theorem exists_regular_relations_at_geometricPoint
    (I : Ideal (GeometricPointSource k K a))
    (v : Fin n → Localization.AtPrime (rationalPointIdeal a))
    (hv : I.map (geometricPointLocalizationMap k K a) = Ideal.span (Set.range v))
    [IsArtinianRing (Localization.AtPrime (rationalPointIdeal a) ⧸
      I.map (geometricPointLocalizationMap k K a))]
    [Nontrivial (Localization.AtPrime (rationalPointIdeal a) ⧸
      I.map (geometricPointLocalizationMap k K a))] :
    ∃ rs : List (GeometricPointSource k K a), rs.length = n ∧ Ideal.ofList rs = I ∧
      RingTheory.Sequence.IsRegular (GeometricPointSource k K a) rs := by
  let S := Localization.AtPrime (rationalPointIdeal a)
  let := (geometricPointLocalizationMap k K a).toAlgebra
  have : IsLocalHom (algebraMap (GeometricPointSource k K a) S) :=
    geometricPointLocalizationMap_isLocalHom k K a
  have : Module.Flat (GeometricPointSource k K a) S :=
    geometricPointLocalizationMap_flat k K a
  have : Module.FaithfullyFlat (GeometricPointSource k K a) S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Finite (GeometricPointSource k K a) I :=
    Module.Finite.of_fg (IsNoetherian.noetherian I)
  obtain ⟨rs, hlen, hrs⟩ := I.exists_ofList_of_map_eq_span S v hv
  have hm : Ideal.ofList (rs.map (geometricPointLocalizationMap k K a)) =
      I.map (geometricPointLocalizationMap k K a) := by rw [← Ideal.map_ofList, hrs]
  have : IsArtinianRing (S ⧸ Ideal.ofList (rs.map (geometricPointLocalizationMap k K a))) := by
    rw [hm]; infer_instance
  have : Nontrivial (S ⧸ Ideal.ofList (rs.map (geometricPointLocalizationMap k K a))) := by
    rw [hm]; infer_instance
  refine ⟨rs, hlen, hrs, (RingTheory.Sequence.isRegular_iff_of_faithfullyFlat (S := S)).mp ?_⟩
  exact isRegular_parameters_at_rationalPoint a _ (by simpa using hlen)

end MvPolynomial
