/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicOriginalPrescribedNormalizedCover
public import FLT.Mazur.PolygonCompleteNormalizedSubgroupCover

/-!
# Complete-family normalized covers retain the original generator

On smooth base changes where three is invertible, the actual odd normalized
atlas subgroup compares with the direct complete-family subgroup pullback.
The chosen universal generator is the original complete generator, and all
its powers are retained by the same full compatible comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "B" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "P" => completeOriginalGenerator K n h

/-- The direct complete subgroup cover identifies the chosen normalized and original generators. -/
theorem completeOriginal_exists_prescribed_odd_normalized_cover {T : Scheme} (g : T ⟶ B)
    [Smooth ((E).baseChange g).curve.hom] (h₃ : IsUnit (3 : Γ(T, ⊤))) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T)
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n true),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n true).baseChange (q i))
        ((H).baseChange (C.f i ≫ g)),
        pullSection (q i) (oddNormalizedGenerator n) ≫ a.subgroup.hom =
          pullSection (C.f i ≫ g) (P) := by
  obtain ⟨C, q, hq⟩ := OddWeierstrassParameter.exists_prescribed_normalized_fppf_cover
    ((H).baseChange g)
    ((completeOriginalGenerator_isCartierGenerator K n h).baseChange (H) g) h₃
  refine ⟨C, q, fun i ↦ ?_⟩
  obtain ⟨a, ha⟩ := hq i
  refine ⟨a.trans (compatibleBaseChangeComp (H) g (C.f i)).symm, ?_⟩
  change _ ≫ (a.subgroup.hom ≫ (compatibleBaseChangeComp (H) g (C.f i)).subgroup.inv) = _
  rw [← Category.assoc, ha]
  exact compatibleBaseChangeComp_inv_section (H) g (C.f i) (P)

/-- The specified normalized powers recover every original complete-family generator power. -/
theorem completeOriginal_prescribed_odd_normalized_pow {T : Scheme} (g : T ⟶ B)
    (q : T ⟶ normalizedLocus n true)
    (a : CompatibleIso ((normalizedSubgroup n true).baseChange q) ((H).baseChange g))
    (ha : pullSection q (oddNormalizedGenerator n) ≫ a.subgroup.hom = pullSection g (P))
    (m : ℕ) :
    (pullSection q (oddNormalizedGenerator n) ^ m) ≫ a.subgroup.hom =
      pullSection g ((P) ^ m) :=
  OddWeierstrassParameter.prescribed_normalized_generator_pow (H) g q a ha m

end FLT.Mazur.PolygonInfinitesimalStages
