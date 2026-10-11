/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafAdicStalkSeparation
public import FLT.Mazur.CoherentIdealIntersection
public import FLT.Mazur.ProperLocalFiberCover

/-!
# Adic ideal separation for a proper family over a local base

An ideal contained in all powers of an extended base ideal vanishes when
the base ideal contains the closed point in its support. Krull intersection
handles the closed fiber and properness eliminates the remaining support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.ProperLocalAdic
open FCurve AnnihilatorSubsheaf FCurve.CoherentDevissage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
  [IsLocallyNoetherian X] (p : X ⟶ Spec R) [IsProper p]
  (I : (Spec R).IdealSheafData) (hI : IsLocalRing.closedPoint R ∈ I.support)

include hI

/-- A proper family has no full ideal invisible on every base-ideal thickening. -/
theorem ideal_eq_bot_of_le_powers (J : X.IdealSheafData)
    (hJ : ∀ m : ℕ, J ≤ I.comap p ^ (m + 1)) : J = ⊥ := by
  let _ := CoherentIdealIntersection.idealModule_coherent J
  let U : X.Opens :=
    ⟨(support (idealModule J))ᶜ, (isClosed_support (idealModule J)).isOpen_compl⟩
  have hU : U = ⊤ := by
    apply Approximation.eq_top_of_contains_proper_closedFiber p
    rintro _ ⟨x, rfl⟩
    change ¬ ¬ Limits.IsZero ((stalk (p.fiberι (IsLocalRing.closedPoint R) x)).obj
      (idealModule J))
    apply not_not.mpr
    apply idealModule_stalk_isZero_of_stalkIdeal_eq_bot
    apply stalkIdeal_eq_bot_of_le_powers _ J hJ
    rw [Scheme.IdealSheafData.support_comap]
    change p (p.fiberι (IsLocalRing.closedPoint R) x) ∈ I.support
    have he : p (p.fiberι (IsLocalRing.closedPoint R) x) =
        IsLocalRing.closedPoint R := ((p.fiberHomeo (IsLocalRing.closedPoint R)) x).property
    exact he.symm ▸ hI
  apply idealSheaf_eq_of_stalkIdeal_eq
  intro x
  rw [stalkIdeal_bot]
  have hx : x ∈ U := by rw [hU]; trivial
  have hz : Limits.IsZero ((stalk x).obj (idealModule J)) := not_not.mp hx
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  apply bot_unique
  rintro _ ⟨v, rfl⟩
  change idealStalkInclusion J x v = 0
  rw [hs.elim v 0, map_zero]

/-- A closed immersion containing every actual adic thickening is an isomorphism. -/
theorem closedImmersion_isIso_of_factors {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j]
    (hl : ∀ m : ℕ, ∃ l : (I.comap p ^ (m + 1)).subscheme ⟶ Z,
      l ≫ j = (I.comap p ^ (m + 1)).subschemeι) : IsIso j := by
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply ideal_eq_bot_of_le_powers p I hI
  intro m
  obtain ⟨l, hl⟩ := hl m
  have hk := l.le_ker_comp j
  rwa [hl, Scheme.IdealSheafData.ker_subschemeι] at hk

end FLT.Mazur.ProperLocalAdic
