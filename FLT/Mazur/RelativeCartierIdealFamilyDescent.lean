/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealFppfFamilyDescent
public import FLT.Mazur.RelativePicardFppfPairs

/-!
# Full ideal descent on relative total spaces

Matching on the actual base overlap tests gives matching on the total-space
overlaps through their canonical isomorphisms. Effective Cartier descent then
recovers every original ideal exactly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (T : Over S)
  (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (I : ∀ i, (pullback f (relativeCoverMember T 𝒰 i).hom).IdealSheafData)

/-- Matching on base pair tests is matching on the original total-space overlaps. -/
theorem relativeCartierIdeal_pair_matching
    (h : ∀ i j, (I i).comap (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j)) =
      (I j).comap (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))) (i j : 𝒰.I₀) :
    (I i).comap (pullback.fst ((relativeTotalCover f T 𝒰).f i)
      ((relativeTotalCover f T 𝒰).f j)) =
    (I j).comap (pullback.snd ((relativeTotalCover f T 𝒰).f i)
      ((relativeTotalCover f T 𝒰).f j)) := by
  have H := congrArg
    (fun J ↦ J.comap (relativeCoverPairTotalIso f T 𝒰 i j).inv) (h i j)
  simpa only [← Scheme.IdealSheafData.comap_comp,
    relativeCoverPairTotalIso_inv_fst, relativeCoverPairTotalIso_inv_snd] using H

/-- Compatible full Cartier ideals on relative tests have a unique global full ideal. -/
theorem existsUnique_relativeCartierIdeal_family_descent
    (hI : ∀ i, EffectiveCartier (I i))
    (h : ∀ i j, (I i).comap (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j)) =
      (I j).comap (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))) :
    ∃! J : (pullback f T.hom).IdealSheafData, EffectiveCartier J ∧
      ∀ i, J.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) = I i :=
  existsUnique_cartierIdeal_family_descent (relativeTotalCover f T 𝒰) I hI
    (relativeCartierIdeal_pair_matching f T 𝒰 I h)

end FLT.Mazur.FCurve
