/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRotatedIdentityOverlap

/-!
# Original markings and closed torus squares on the translated atlas

Each chart carries the original cyclic marking, and its closed torus inclusion
forms the actual Cartesian square with the original closed polygon. These
retain the labeled sections and scheme structures needed for group gluing.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeClosedFiberInclusion completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (a : ZMod n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "U" => completePointIdentityOpen K n h i
local notation "V" => completeRotatedIdentityOpen K n h i a
local notation "j" => completeClosedFiberInclusion K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "t" => Over.Hom.left
  (torusToComponent K ≫ componentι K n (rotateIndex a i) ≫ p)

/-- The original identity marking transported to its actual rotated chart. -/
def completeRotatedIdentityMarking : S₀ ⟶ (V).toScheme :=
  completePointIdentityMarking K n h i ≫ (completeRotatedIdentityIso K n h i a).inv

/-- The transported marking is exactly the original marking with the translated label. -/
@[reassoc] theorem completeRotatedIdentityMarking_inclusion :
    completeRotatedIdentityMarking K n h i a ≫ (V).ι =
      completeBaseMarking K n h (rotateIndex a i) := by
  rw [completeRotatedIdentityMarking, Category.assoc,
    completeRotatedIdentityIso_inv_inclusion, completePointIdentityMarking_inclusion_assoc,
    completeBaseMarking_rotation]

/-- The original cyclic marking lies in the corresponding full rotated chart. -/
theorem completeBaseMarking_range_rotatedIdentity :
    Set.range (completeBaseMarking K n h (rotateIndex a i)) ⊆ (V) := by
  rintro _ ⟨x, rfl⟩
  have he := congrArg (fun v ↦ v x) (completeRotatedIdentityMarking_inclusion K n h i a)
  rw [← he]
  exact (completeRotatedIdentityMarking K n h i a x).2

/-- The full translated closed Laurent component lifted to its original translated chart. -/
def completeRotatedIdentityClosedTorus : (MultiplicativeGroupScheme.gm K).left ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι ((t) ≫ (j)) (by
    let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (t) x ∈ (j) ⁻¹ᵁ (V)
    rw [completeRotatedIdentityOpen_closed_preimage]
    exact ⟨x, rfl⟩)

/-- The closed chart inclusion retains its actual original Laurent normalization map. -/
@[reassoc] theorem completeRotatedIdentityClosedTorus_inclusion :
    completeRotatedIdentityClosedTorus K n h i a ≫ (V).ι = (t) ≫ (j) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The translated Laurent component is precisely the scheme-theoretic closed chart fiber. -/
theorem completeRotatedIdentityClosedTorus_isPullback :
    IsPullback (completeRotatedIdentityClosedTorus K n h i a) (t) (V).ι (j) := by
  let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
  apply IsOpenImmersion.isPullback
  · exact (completeRotatedIdentityClosedTorus_inclusion K n h i a).symm
  · rw [Scheme.Opens.opensRange_ι]
    exact completeRotatedIdentityOpen_closed_preimage K n h i a

/-- Chart coordinates on each closed torus retain the original Laurent parameter. -/
@[reassoc] theorem completeRotatedIdentityClosedTorus_coordinates :
    completeRotatedIdentityClosedTorus K n h i a ≫
      (completeRotatedIdentityIso K n h i a).hom =
        completePointIdentityClosedTorus K n h i := by
  apply (cancel_mono (U).ι).mp
  rw [Category.assoc, completeRotatedIdentityIso_inclusion,
    completeRotatedIdentityClosedTorus_inclusion_assoc,
    completePointIdentityClosedTorus_inclusion,
    completeClosedTorus_rotation, ← rotateIndex_add,
    add_neg_cancel, rotateIndex_zero]

end FLT.Mazur.PolygonInfinitesimalStages
