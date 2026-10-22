/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameCover

/-!
# Original marking-frame neighborhoods on arbitrary test schemes

An affine neighborhood in the test refines the inverse image of an original
framed chart. All such factorizations form a cover without imposing any
Noetherian, affine or separated condition on the whole test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (g : T ⟶ S)

/-- An actual affine test open factoring through an original marking frame. -/
structure SmoothMarkingTestChart where
  /-- The affine open in the original test scheme. -/
  base : T.affineOpens
  /-- The original independently framed affine chart. -/
  original : SmoothMarkingAffineChart E s
  /-- The actual factorization through the original chart base. -/
  map : base.1.toScheme ⟶ original.base.1.toScheme
  /-- The factorization retains the prescribed test morphism. -/
  fac : map ≫ original.base.1.ι = base.1.ι ≫ g

instance smoothMarkingTestChart_affine (c : SmoothMarkingTestChart E s g) :
    IsAffine c.base.1.toScheme := c.base.2

/-- Actual factorizations refine every neighborhood of every test point. -/
theorem exists_smoothMarkingTestChart {V : T.Opens} {x : T} (hx : x ∈ V) :
    ∃ c : SmoothMarkingTestChart E s g, x ∈ c.base.1 ∧ c.base.1 ≤ V := by
  obtain ⟨i, hi, _⟩ := exists_smoothMarkingAffineChart E s
    (show g x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V ⊓ g ⁻¹ᵁ i.base.1 from ⟨hx, hi⟩)
  let hle : U ≤ g ⁻¹ᵁ i.base.1 := hUV.trans inf_le_right
  refine ⟨⟨⟨U, hU⟩, i, T.homOfLE hle ≫ g ∣_ i.base.1, ?_⟩,
    hxU, hUV.trans inf_le_left⟩
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- The actual factored affine neighborhoods cover the entire unrestricted test scheme. -/
def smoothMarkingTestCover : T.OpenCover where
  I₀ := SmoothMarkingTestChart E s g
  X c := c.base.1.toScheme
  f c := c.base.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, _⟩ := exists_smoothMarkingTestChart E s g
      (show x ∈ (⊤ : T.Opens) from trivial)
    exact ⟨c, ⟨x, hc⟩, rfl⟩

/-- The cover has arbitrarily small members, even when the test is nonseparated. -/
theorem smoothMarkingTestCover_isBasis :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun c ↦ ((smoothMarkingTestCover E s g).f c).opensRange)) := by
  apply TopologicalSpace.Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨c, hc, hle⟩ := exists_smoothMarkingTestChart E s g hx
  exact ⟨c.base.1, ⟨c, Scheme.Opens.opensRange_ι _⟩, hc, hle⟩

end FLT.Mazur.GeneralizedEllipticCurve
