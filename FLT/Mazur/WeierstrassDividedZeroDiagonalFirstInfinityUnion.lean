/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalInfinityIntersection
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# The actual first initial/infinity open union after diagonal correction

The complete original D(q) gives the pushout presentation of this source
open union. Its inclusion retains both original corrected chart maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu false
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "c" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

instance arithmeticZeroDiagonalOverlapToInfinity_isOpenImmersion : IsOpenImmersion i := by
  exact MorphismProperty.of_isPullback
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false).flip
    (inferInstanceAs (IsOpenImmersion (c (.initial false))))

instance arithmeticZeroDiagonalInitialOverlap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu b) := by
  exact MorphismProperty.of_isPullback
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu b)
    (inferInstanceAs (IsOpenImmersion (c .infinity)))

/-- The full first initial/infinity pair is glued along its original complete intersection. -/
def arithmeticZeroDiagonalFirstInfinityPushout : Scheme := pushout i l

/-- This pair maps into the actual original corrected global stage. -/
def arithmeticZeroDiagonalFirstInfinityToGlobal :
    arithmeticZeroDiagonalFirstInfinityPushout hπ data H m hj u hu ⟶ X :=
  pushout.desc (c .infinity) (c (.initial false))
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false).w

local notation "f" => arithmeticZeroDiagonalFirstInfinityToGlobal hπ data H m hj u hu

instance arithmeticZeroDiagonalFirstInfinityToGlobal_isOpenImmersion : IsOpenImmersion f :=
  SchemeOpenPushout.coverDesc_isOpenImmersion i l (c .infinity) (c (.initial false))
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false)

/-- The pushout retains the entire original infinity chart inclusion. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityToGlobal_infinity :
    pushout.inl i l ≫ f = c .infinity := pushout.inl_desc _ _ _

/-- The pushout retains the entire first corrected initial chart inclusion. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityToGlobal_initial :
    pushout.inr i l ≫ f = c (.initial false) := pushout.inr_desc _ _ _

/-- The pair has exactly the union of the two complete original chart images. -/
theorem arithmeticZeroDiagonalFirstInfinityToGlobal_range :
    Set.range f = Set.range (c .infinity) ∪ Set.range (c (.initial false)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover i l x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, (congrArg (fun k ↦ k a)
        (arithmeticZeroDiagonalFirstInfinityToGlobal_infinity hπ data H m hj u hu)).symm⟩
    · exact Or.inr ⟨a, (congrArg (fun k ↦ k a)
        (arithmeticZeroDiagonalFirstInfinityToGlobal_initial hπ data H m hj u hu)).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨pushout.inl i l a, congrArg (fun k ↦ k a)
        (arithmeticZeroDiagonalFirstInfinityToGlobal_infinity hπ data H m hj u hu)⟩
    · exact ⟨pushout.inr i l a, congrArg (fun k ↦ k a)
        (arithmeticZeroDiagonalFirstInfinityToGlobal_initial hπ data H m hj u hu)⟩

/-- The specified open union inside the actual source arithmetic stage. -/
def arithmeticZeroDiagonalFirstInfinityUnion : (X).Opens :=
  (c .infinity).opensRange ⊔ (c (.initial false)).opensRange

/-- The complete pushout is the actual source open union, without additional identifications. -/
def arithmeticZeroDiagonalFirstInfinityUnionIso :
    arithmeticZeroDiagonalFirstInfinityPushout hπ data H m hj u hu ≅
      (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).toScheme :=
  IsOpenImmersion.isoOfRangeEq f
    (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).ι (by
      rw [Scheme.Opens.range_ι, arithmeticZeroDiagonalFirstInfinityToGlobal_range]
      rfl)

/-- The union identification recovers its original global inclusion. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionIso_global :
    (arithmeticZeroDiagonalFirstInfinityUnionIso hπ data H m hj u hu).hom ≫
      (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).ι = f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.WeierstrassDividedDepth
