/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericIdealInjection

/-!
# Support and multiplicity one for the generic ideal embedding

The constructed cokernel omits the closed generic point. With the original
support bound its support is strictly smaller than the integral closed image.
The chosen generic basis has one element under the original residue-dimension
hypothesis, giving an embedding of a single actual ideal module.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericCoordinates FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.GenericIdealInjection
open FLT.Mazur.CoherentGenericIdealEmbedding

universe u

namespace FLT.Mazur.GenericIdealSupport

variable {X : Scheme.{u}}

/-- An actual ideal module stays coherent after closed pushforward. -/
instance closedIdeal_coherent [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (I : J.subscheme.IdealSheafData) :
    ((pushforward J.subschemeι).obj (idealModule I)).IsFinitePresentation := by
  have := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have := idealModule_coherent I
  exact closedPushforward_isFinitePresentation J.subschemeι (idealModule I)

/-- A comparison invertible at a point has strictly smaller cokernel support in any bound
containing that point and the target support. -/
theorem cokernel_support_ssubset {M N : X.Modules} (f : M ⟶ N) (x : X)
    [IsIso ((stalk x).map f)] (Z : Set X) (hx : x ∈ Z) (hN : support N ⊆ Z) :
    support (cokernel f) ⊂ Z := by
  refine ⟨(support_subset_of_epi (cokernel.π f)).trans hN, ?_⟩
  intro h
  exact ((isIso_stalk_iff_notMem_support f x).mp inferInstance).2 (h hx)

/-- The constructed embedding has an actual comparison open and a closed, smaller error support. -/
theorem exists_supported_embedding [IsNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme)))
    (hs : support F ⊆ Set.range J.subschemeι) :
    ∃ (I : J.subscheme.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      (pushforward J.subschemeι).obj (idealSum I
        (Module.finrank J.subscheme.functionField
          ((CoherentClosedReduction.descent J F).presheaf.stalk (genericPoint J.subscheme)))) ⟶ F,
      CoherentSequence (ShortComplex.cokernelSequence f) ∧
      J.subschemeι (genericPoint J.subscheme) ∈ comparisonOpen f ∧
      IsClosed (support (cokernel f)) ∧
      support (cokernel f) ⊂ Set.range J.subschemeι := by
  obtain ⟨I, hI, f, hf, hη, hseq⟩ := exists_closed_ideal_embedding J F hF
  have : (cokernel f).IsFinitePresentation := hseq.finite₃
  exact ⟨I, hI, f, hseq, (mem_comparisonOpen_iff f _).mpr hη,
    isClosed_support _, cokernel_support_ssubset f _ _ ⟨genericPoint J.subscheme, rfl⟩ hs⟩

/-- A finite sum with one term is canonically the original ideal module. -/
def idealSumOneIso (I : X.IdealSheafData) : idealSum I 1 ≅ idealModule I :=
  coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ idealModule I)

/-- The residue-dimension hypothesis specializes the constructed source to one actual ideal. -/
theorem exists_rank_one_embedding [IsNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme)))
    (hd : letI := residueModule F _ hF
      Module.finrank (X.residueField (J.subschemeι (genericPoint J.subscheme)))
        (F.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) = 1) :
    ∃ (I : J.subscheme.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      (pushforward J.subschemeι).obj (idealModule I) ⟶ F,
      Mono f ∧ IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map f) ∧
      CoherentSequence (ShortComplex.cokernelSequence f) := by
  have he := exists_closed_ideal_embedding J F hF
  rw [comparison_rank_one J F hF hd] at he
  obtain ⟨I, hI, f, hf, hη, _⟩ := he
  let e := (pushforward J.subschemeι).mapIso (idealSumOneIso I)
  refine ⟨I, hI, e.inv ≫ f, inferInstance, ?_, coherent_cokernelSequence _⟩
  rw [Functor.map_comp]
  infer_instance

/-- In the supported multiplicity-one case, the single-ideal cokernel has smaller support. -/
theorem exists_supported_rank_one_embedding [IsNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme)))
    (hd : letI := residueModule F _ hF
      Module.finrank (X.residueField (J.subschemeι (genericPoint J.subscheme)))
        (F.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) = 1)
    (hs : support F ⊆ Set.range J.subschemeι) :
    ∃ (I : J.subscheme.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      (pushforward J.subschemeι).obj (idealModule I) ⟶ F,
      CoherentSequence (ShortComplex.cokernelSequence f) ∧
      J.subschemeι (genericPoint J.subscheme) ∈ comparisonOpen f ∧
      IsClosed (support (cokernel f)) ∧
      support (cokernel f) ⊂ Set.range J.subschemeι ∧
      support (cokernel f) ⊂ support F := by
  obtain ⟨I, hI, f, hf, hη, hseq⟩ := exists_rank_one_embedding J F hF hd
  have : (cokernel f).IsFinitePresentation := hseq.finite₃
  have hx : J.subschemeι (genericPoint J.subscheme) ∈ support F := by
    obtain ⟨m, hm, _, _⟩ := exists_cyclic_generator F _ hF hd
    intro hz
    exact hm ((AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim m 0)
  exact ⟨I, hI, f, hseq, (mem_comparisonOpen_iff f _).mpr hη,
    isClosed_support _, cokernel_support_ssubset f _ _ ⟨genericPoint J.subscheme, rfl⟩ hs,
    cokernel_support_ssubset f _ _ hx (Set.Subset.refl _)⟩

end FLT.Mazur.GenericIdealSupport
