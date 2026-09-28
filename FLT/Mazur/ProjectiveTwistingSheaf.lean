/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafUnitCocycleRestrict
public import FLT.Mazur.ProjectiveTwistCocycle

/-!
# Twisting sheaves on polynomial projective space

The sheaf is constructed from compatible chart coefficients. With the basis
convention `eᵢ = Xᵢⁿ`, these satisfy `sᵢ = (Xⱼ/Xᵢ)ⁿ sⱼ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The polynomial coordinate transitions, restricted to every common subopen. -/
def twistCocycle (n : ℤ) : Cocycle (chart R ι) :=
  Cocycle.ofOverlap (twistTransition R ι n) (twistTransition_self R ι n) (by
    intro i j k V hi hj hk
    have h := congrArg (restrictUnits R ι (le_inf (le_inf hi hj) hk))
      (twistTransition_cocycle R ι n i j k)
    simp only [map_mul, restrictUnits_comp] at h
    exact congrArg Units.val h)

/-- The twisting sheaf, descended from the explicit polynomial coordinate cocycle. -/
def twistingSheaf (n : ℤ) : (space R ι).Modules := (twistCocycle R ι n).sheaf

/-- The usual `O(n)` on projective `d`-space. -/
abbrev O (A : Type) [CommRing A] (d : ℕ) (n : ℤ) :
    (space A (Fin (d + 1))).Modules := twistingSheaf A (Fin (d + 1)) n

/-- Each standard chart trivializes the twisting sheaf by coefficient evaluation. -/
def twistingSheafRestrictIso (n : ℤ) (i : ι) :
    (twistingSheaf R ι n).restrict (chart R ι i).ι ≅
      structureModule (chart R ι i).toScheme := (twistCocycle R ι n).restrictIso i

/-- Every integer twist is locally free of rank one. -/
theorem twistingSheaf_locallyFreeRankOne (n : ℤ) :
    LocallyFreeRankOne (twistingSheaf R ι n) :=
  (twistCocycle R ι n).locallyFreeRankOne (iSup_chart R ι)

/-- The transition coefficient on a common subopen is the restricted power of the ratio. -/
lemma twistCocycle_unit (n : ℤ) (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j) :
    (twistCocycle R ι n).unit i j V hi hj =
      restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ n := by
  change restrictUnits R ι (le_inf hi hj)
    (restrictUnits R ι (chart_inf R ι i j).le
      (Units.map _ (ratioUnit R ι i j ^ n))) = _
  simp only [map_zpow, twistTransition, transitionSection, transitionUnit_one]

/-- The coefficient equation `sᵢ = (Xⱼ/Xᵢ)ⁿ sⱼ` on every common subopen. -/
theorem twistingSheaf_transition (n : ℤ) (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (s : (twistCocycle R ι n).sections V) :
    (twistCocycle R ι n).evaluate i hi s =
      ((restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ n :
        Γ(space R ι, V)ˣ) : Γ(space R ι, V)) * (twistCocycle R ι n).evaluate j hj s := by
  rw [← twistCocycle_unit]
  exact (twistCocycle R ι n).transition i j hi hj s

/-- The actual sheaf trivializations have the specified change-of-chart formula. -/
theorem twistingSheaf_change (n : ℤ) (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j) (W : V.toScheme.Opens)
    (r : Γ(V.toScheme, W)) :
    (((twistCocycle R ι n).onOpenIso j V hj).inv ≫
      ((twistCocycle R ι n).onOpenIso i V hi).hom).app W r =
      ((restrictUnits R ι (le_inf ((V.ι_image_le W).trans hi)
        ((V.ι_image_le W).trans hj)) (twistTransition R ι 1 i j) ^ n :
          Γ(space R ι, V.ι ''ᵁ W)ˣ) : Γ(space R ι, V.ι ''ᵁ W)) *
            (show Γ(space R ι, V.ι ''ᵁ W) from r) := by
  rw [← twistCocycle_unit]
  exact (twistCocycle R ι n).onOpenIso_change i j V hi hj W r

@[simp] lemma twistCocycle_zero_unit (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j) :
    (twistCocycle R ι 0).unit i j V hi hj = 1 := by
  rw [twistCocycle_unit, zpow_zero]

/-- Restriction of a regular function gives compatible coefficients for the zero twist. -/
def zeroTwistSections (V : (space R ι).Opens) :
    Γ(space R ι, V) →+ (twistCocycle R ι 0).sections V where
  toFun r := ⟨fun i ↦ res inf_le_left r, by
    intro i j W hi hj
    simp only [res_res, twistCocycle_zero_unit, Units.val_one, one_mul]⟩
  map_zero' := by ext i; exact map_zero _
  map_add' _ _ := by ext i; exact map_add _ _ _

/-- The sheaf gluing theorem identifies zero-twist tuples with regular functions. -/
lemma zeroTwistSections_bijective (V : (space R ι).Opens) :
    Function.Bijective (zeroTwistSections R ι V) := by
  have hcover : V ≤ ⨆ i, V ⊓ chart R ι i := by
    rw [← inf_iSup_eq, iSup_chart, inf_top_eq]
  constructor
  · intro r s h
    apply (space R ι).sheaf.eq_of_locally_eq' (fun i ↦ V ⊓ chart R ι i) V
      (fun _ ↦ homOfLE inf_le_left) hcover
    intro i
    exact congrArg (fun t : (twistCocycle R ι 0).sections V ↦ t.1 i) h
  · intro s
    obtain ⟨r, hr, _⟩ := (space R ι).sheaf.existsUnique_gluing'
      (fun i ↦ V ⊓ chart R ι i) V (fun _ ↦ homOfLE inf_le_left) hcover s.1 (by
        intro i j
        change res inf_le_left (s.1 i) = res inf_le_right (s.1 j)
        simpa only [twistCocycle_zero_unit, Units.val_one, one_mul] using
          s.2 i j ((V ⊓ chart R ι i) ⊓ (V ⊓ chart R ι j)) inf_le_left inf_le_right)
    exact ⟨r, Subtype.ext (funext hr)⟩

/-- The zero twist is canonically the structure module. -/
def twistingSheafZeroIso : twistingSheaf R ι 0 ≅ structureModule (space R ι) := by
  refine ((SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)).symm
  · refine ModuleCat.isoMk (AddEquiv.toAddCommGrpIso
      (AddEquiv.ofBijective (zeroTwistSections R ι V.unop)
        (zeroTwistSections_bijective R ι V.unop))) ?_
    intro (r : Γ(space R ι, V.unop))
    ext (s : Γ(space R ι, V.unop))
    apply Subtype.ext
    funext i
    change res inf_le_left r * res inf_le_left s = res inf_le_left (r * s)
    exact (map_mul (res inf_le_left) r s).symm
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext i
    change res _ (res _ s) = res _ (res _ s)
    simp only [res_res]

/-- The standard-chart trivialization of `O(n)` on projective `d`-space. -/
def ORestrictIso (A : Type) [CommRing A] (d : ℕ) (n : ℤ) (i : Fin (d + 1)) :
    (O A d n).restrict (chart A (Fin (d + 1)) i).ι ≅
      structureModule (chart A (Fin (d + 1)) i).toScheme :=
  twistingSheafRestrictIso A (Fin (d + 1)) n i

/-- The twisting sheaves on finite-dimensional projective space have local rank one. -/
theorem O_locallyFreeRankOne (A : Type) [CommRing A] (d : ℕ) (n : ℤ) :
    LocallyFreeRankOne (O A d n) := twistingSheaf_locallyFreeRankOne A (Fin (d + 1)) n

/-- The degree-zero twisting sheaf on projective `d`-space is the structure module. -/
def OZeroIso (A : Type) [CommRing A] (d : ℕ) :
    O A d 0 ≅ structureModule (space A (Fin (d + 1))) :=
  twistingSheafZeroIso A (Fin (d + 1))

end FLT.Mazur.ProjectiveSpace
