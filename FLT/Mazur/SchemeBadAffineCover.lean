/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A constructed finite affine cover of an open complement

The closed complement is given its reduced induced scheme structure, then
covered by finitely many actual affine schemes. The ambient scheme need not
be affine. Reduction is used only for testing support, never for section lifting.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
variable {X : Scheme} (O : X.Opens)

/-- The closed bad locus with its reduced induced structure. -/
def badScheme : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩).subscheme

/-- The actual closed inclusion of the bad locus. -/
def badInclusion : badScheme O ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩).subschemeι

instance badInclusion_isClosedImmersion : IsClosedImmersion (badInclusion O) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩).subschemeι)

/-- The construction retains exactly all bad points. -/
theorem badInclusion_range : Set.range (badInclusion O) = (O : Set X)ᶜ := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

variable [NoetherianSpace X]

instance badScheme_noetherianSpace : NoetherianSpace (badScheme O) :=
  (badInclusion O).isClosedEmbedding.isInducing.noetherianSpace

/-- A finite affine atlas of the constructed bad scheme. -/
def badCover : (badScheme O).OpenCover := (badScheme O).affineCover.finiteSubcover

instance badCoverFintype : Fintype (badCover O).I₀ :=
  inferInstanceAs (Fintype (badScheme O).affineCover.finiteSubcover.I₀)

instance badCover_isAffine (i : (badCover O).I₀) : IsAffine ((badCover O).X i) :=
  isAffine_Spec _

/-- Each affine bad chart maps to the original ambient scheme. -/
def badChartMap (i : (badCover O).I₀) : (badCover O).X i ⟶ X :=
  (badCover O).f i ≫ badInclusion O

/-- Every point of every chart is an actual bad ambient point. -/
theorem badChartMap_not_mem (i : (badCover O).I₀) (x : (badCover O).X i) :
    badChartMap O i x ∉ O := by
  apply (badInclusion_range O).le
  exact ⟨(badCover O).f i x, rfl⟩

/-- Every bad ambient point has a lift to one of the finitely many affine charts. -/
theorem exists_badChart_lift (x : X) (hx : x ∉ O) :
    ∃ (i : (badCover O).I₀) (y : (badCover O).X i), badChartMap O i y = x := by
  obtain ⟨b, rfl⟩ := (badInclusion_range O).ge hx
  obtain ⟨i, y, hy⟩ := (badCover O).exists_eq b
  exact ⟨i, y, congrArg (badInclusion O) hy⟩

end FLT.Mazur.SchemeBadAffineCover
