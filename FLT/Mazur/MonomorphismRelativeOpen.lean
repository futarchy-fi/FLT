/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismOpenImage
public import FLT.Mazur.SchemeWholeFiberOpen

/-!
# Actual inverse models over whole fibers of an unchanged target

For a monomorphism into a relative kernel, construct the largest target open
whose complete kernel lies in its open inverse locus. The comparison is an
isomorphism over that open, with an actual original-source inverse. This does
not assert that the constructed target open is nonempty or covers the target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
set_option backward.isDefEq.respectTransparency false
variable {D K T : Scheme.{u}} (m : D ⟶ K) [Mono m] (q : K ⟶ T)

/-- An open of the original quotient target, not a reduced kernel stratum. -/
def targetOpen : T.Opens := SchemeWholeFiberOpen.locus q (MonomorphismOpenImage.locus m)

/-- Its whole original kernel open, retaining both endpoints and nilpotents. -/
def kernelOpen : K.Opens := q ⁻¹ᵁ targetOpen m q

omit [Mono m] in
/-- No point of a retained kernel fiber lies outside the original inverse locus. -/
theorem kernelOpen_le : kernelOpen m q ≤ MonomorphismOpenImage.locus m :=
  SchemeWholeFiberOpen.preimage_le q _

/-- The actual recovered original relation arrow on the entire retained kernel. -/
def originalLift : (kernelOpen m q).toScheme ⟶ D :=
  K.homOfLE (kernelOpen_le m q) ≫ MonomorphismOpenImage.lift m

/-- The inverse keeps the actual kernel coordinates as scheme morphisms. -/
@[reassoc]
theorem originalLift_comp : originalLift m q ≫ m = (kernelOpen m q).ι := by
  rw [originalLift, Category.assoc, MonomorphismOpenImage.lift_comp, Scheme.homOfLE_ι]

/-- Lift back into the whole inverse image of the retained kernel open. -/
def inverse : (kernelOpen m q).toScheme ⟶ (m ⁻¹ᵁ kernelOpen m q).toScheme :=
  (isPullback_morphismRestrict m (kernelOpen m q)).lift (𝟙 _) (originalLift m q)
    (by rw [Category.id_comp, originalLift_comp])

@[reassoc]
theorem inverse_projection : inverse m q ≫ m ∣_ kernelOpen m q = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

@[reassoc]
theorem inverse_original : inverse m q ≫ (m ⁻¹ᵁ kernelOpen m q).ι = originalLift m q :=
  IsPullback.lift_snd _ _ _ _

/-- An effective comparison on the entire retained target open, with unreduced structure. -/
def comparisonIso : (m ⁻¹ᵁ kernelOpen m q).toScheme ≅ (kernelOpen m q).toScheme where
  hom := m ∣_ kernelOpen m q
  inv := inverse m q
  hom_inv_id := by
    let _ := (isPullback_morphismRestrict m (kernelOpen m q)).mono_fst_of_mono
    apply (cancel_mono (m ∣_ kernelOpen m q)).mp
    rw [Category.assoc, inverse_projection, Category.comp_id, Category.id_comp]
  inv_hom_id := inverse_projection m q

/-- The isomorphism recovers the original source map, including its coefficient map. -/
@[reassoc]
theorem comparisonIso_inv_original : (comparisonIso m q).inv ≫
    (m ⁻¹ᵁ kernelOpen m q).ι = originalLift m q := inverse_original m q

/-- Every original kernel test over the target open has a unique full original arrow. -/
theorem test_lift {Z : Scheme.{u}} (a : Z ⟶ K)
    (ha : Set.range (a ≫ q) ⊆ targetOpen m q) :
    ∃! b : Z ⟶ D, b ≫ m = a := by
  have h : Set.range a ⊆ (kernelOpen m q).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    rintro _ ⟨z, rfl⟩
    exact ha ⟨z, rfl⟩
  let t := IsOpenImmersion.lift (kernelOpen m q).ι a h
  refine ⟨t ≫ originalLift m q, ?_, ?_⟩
  · dsimp only
    rw [Category.assoc, originalLift_comp]
    exact IsOpenImmersion.lift_fac _ _ _
  · intro b hb
    apply (cancel_mono m).mp
    rw [hb, Category.assoc, originalLift_comp]
    exact (IsOpenImmersion.lift_fac _ _ _).symm

end FLT.Mazur.MonomorphismRelativeOpen
