/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineComparison
public import FLT.Mazur.CyclicCharacteristicInvariantLocalization

/-!
# Canonical principal domains on restricted invariant opens

The canonical spectrum comparison uses exactly the original invariant principal
open. The identification of section rings preserves the actual restriction map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))
local notation "Y" => invariantOpenSpace n W

/-- The canonical principal domain tests the original invariant germ. -/
theorem restrictedPrincipal_mem (z : W) :
    z ∈ (Y).toΓSpecMapBasicOpen ((invariantOpenSectionsIso n W).inv s) ↔
      z.val ∈ invariantPrincipal n W s := by
  rw [LocallyRingedSpace.toΓSpecMapBasicOpen_eq, RingedSpace.mem_top_basicOpen]
  change IsUnit ((Y).presheaf.Γgerm z ((invariantOpenSectionsIso n W).inv s)) ↔
    z.val ∈ (invariantLocallyRingedSpace n).toRingedSpace.basicOpen s
  rw [RingedSpace.mem_basicOpen _ _ _ z.property]
  let e := (invariantLocallyRingedSpace n).restrictStalkIso
    (Opens.isOpenEmbedding (X := space n) W) z
  rw [← isUnit_map_iff e.hom.hom]
  apply (congrArg IsUnit ?_).to_iff
  refine ((invariantLocallyRingedSpace n).restrictStalkIso_hom_eq_germ_apply
    (Opens.isOpenEmbedding (X := space n) W) ⊤ z (by trivial)
    ((invariantOpenSectionsIso n W).inv s)).trans ?_
  change TopCat.Presheaf.germ (invariantSheaf n).obj _ z.val _
    ((invariantSheaf n).obj.map _ s) = _
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Extending the restricted principal domain recovers the original principal open. -/
theorem restrictedPrincipal_image :
    (Opens.isOpenEmbedding (X := space n) W).functor.obj
       ((Y).toΓSpecMapBasicOpen ((invariantOpenSectionsIso n W).inv s)) =
      invariantPrincipal n W s := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (restrictedPrincipal_mem n W s x).mp hx
  · intro hz
    refine ⟨⟨z, invariantPrincipal_le n W s hz⟩, ?_, rfl⟩
    exact (restrictedPrincipal_mem n W s _).mpr hz

/-- Actual principal sections on the restriction and on the ambient open coincide. -/
def restrictedPrincipalSectionsIso :
    (Y).presheaf.obj (op ((Y).toΓSpecMapBasicOpen ((invariantOpenSectionsIso n W).inv s))) ≅
      (invariantSheaf n).obj.obj (op (invariantPrincipal n W s)) :=
  (invariantSheaf n).obj.mapIso (eqToIso (congrArg op (restrictedPrincipal_image n W s)))

/-- The section identification carries the canonical restriction to the original restriction. -/
@[reassoc] theorem restrictedPrincipalSectionsIso_restriction :
    (Y).toToΓSpecMapBasicOpen ((invariantOpenSectionsIso n W).inv s) ≫
      (restrictedPrincipalSectionsIso n W s).hom =
      (invariantOpenSectionsIso n W).hom ≫
        CommRingCat.ofHom (principalRestriction n W s) := by
  change (invariantSheaf n).obj.map _ ≫ (invariantSheaf n).obj.map _ =
    (invariantSheaf n).obj.map _ ≫ (invariantSheaf n).obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end FLT.Mazur.CyclicCharacteristicOrbit
