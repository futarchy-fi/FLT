/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointCartesian
public import FLT.Mazur.CyclicCharacteristicQuotientFiniteType

/-!
# One finite affine cover of the assembled characteristic quotient

The finite combined source index now gives one affine open cover of the
single quotient scheme. All target charts and the assembled target are
finite type over the integers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Each original affine invariant quotient includes into the single quotient target. -/
def disjointAffineQuotientInclusion (i : InvariantAffineIndex n) :
    invariantAffineQuotient n i ⟶ normalizedDisjointQuotient n :=
  invariantAffineQuotientInclusion n i ≫ normalizedDisjointQuotientInclusion n i.1

/-- All selected affine quotient inclusions remain open immersions in the union. -/
instance disjointAffineQuotientInclusion_isOpenImmersion (i : InvariantAffineIndex n) :
    IsOpenImmersion (disjointAffineQuotientInclusion n i) := by
  unfold disjointAffineQuotientInclusion
  infer_instance

/-- The original finite combined chart index covers the single actual quotient scheme. -/
def disjointAffineQuotientCover : (normalizedDisjointQuotient n).OpenCover where
  I₀ := InvariantAffineIndex n
  X i := invariantAffineQuotient n i
  f i := disjointAffineQuotientInclusion n i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨b, x, rfl⟩ := (sigmaOpenCover (normalizedQuotient n)).exists_eq z
    obtain ⟨i, y, rfl⟩ := (normalizedQuotientCover n b).exists_eq x
    exact ⟨⟨b, i⟩, y, rfl⟩

/-- The single quotient cover has finitely many charts. -/
instance disjointAffineQuotientCoverFintype : Fintype (disjointAffineQuotientCover n).I₀ :=
  inferInstanceAs (Fintype (InvariantAffineIndex n))

/-- Every member of the single quotient cover is affine. -/
instance disjointAffineQuotientCover_isAffine (i : (disjointAffineQuotientCover n).I₀) :
    IsAffine ((disjointAffineQuotientCover n).X i) := invariantAffineQuotient_isAffine n i

/-- The integer structure morphism of the single constructed quotient scheme. -/
def normalizedDisjointQuotientToInt : normalizedDisjointQuotient n ⟶ Spec (.of ℤ) :=
  specZIsTerminal.from _

/-- All original selected quotient structure maps agree with the single integer structure. -/
@[reassoc] theorem disjointAffineQuotientInclusion_toInt (i : InvariantAffineIndex n) :
    disjointAffineQuotientInclusion n i ≫ normalizedDisjointQuotientToInt n =
      invariantAffineQuotientToInt n i := specZIsTerminal.hom_ext _ _

/-- The actual single quotient target is locally of finite type over the integers. -/
instance normalizedDisjointQuotientToInt_locallyOfFiniteType :
    LocallyOfFiniteType (normalizedDisjointQuotientToInt n) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (disjointAffineQuotientCover n)
  intro i
  change LocallyOfFiniteType
    (disjointAffineQuotientInclusion n i ≫ normalizedDisjointQuotientToInt n)
  rw [disjointAffineQuotientInclusion_toInt]
  infer_instance

/-- The constructed finite affine cover makes the single quotient quasi-compact. -/
instance normalizedDisjointQuotient_compactSpace : CompactSpace (normalizedDisjointQuotient n) :=
  (disjointAffineQuotientCover n).compactSpace

/-- The single quotient is quasi-compact over the integers. -/
instance normalizedDisjointQuotientToInt_quasiCompact :
    QuasiCompact (normalizedDisjointQuotientToInt n) :=
  (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ => CompactSpace X)).mpr inferInstance

/-- The assembled finite type integer quotient is Noetherian. -/
instance normalizedDisjointQuotient_isNoetherian : IsNoetherian (normalizedDisjointQuotient n) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizedDisjointQuotientToInt n)
  toCompactSpace := inferInstance

end FLT.Mazur.CyclicCharacteristicAtlas
