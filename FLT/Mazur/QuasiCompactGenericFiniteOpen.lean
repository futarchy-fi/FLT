/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactGenericFlatOpen
public import FLT.Mazur.AffineGenericFiniteOpen
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Generic finiteness retaining an entire separated quasi-finite source

A finite affine cover becomes finite over one original principal target open.
Its surjectivity descends universal closedness to the whole original source.
Separatedness and quasi-finiteness then give finiteness by Zariski's main theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.QuasiCompactGenericFlatOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (X : Scheme) [CompactSpace X]

instance affineCoverMap_surjective : Surjective (affineCoverMap X) := by
  unfold affineCoverMap
  infer_instance

instance affineCoverMap_locallyQuasiFinite : LocallyQuasiFinite (affineCoverMap X) := by
  unfold affineCoverMap
  exact IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

variable {X} {R : Type} [CommRing R] [IsDomain R]
  (g : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation g]
  [LocallyQuasiFinite g] [IsSeparated g]
local notation "j" => targetMap g

/-- The whole source, not merely each chosen chart, is finite on the constructed generic open. -/
instance projection_isFinite : IsFinite (pullback.fst j g) := by
  let p := affineCoverMap X
  let e : pullback j (p ≫ g) ⟶ pullback j g :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
      rw [Category.assoc]
      exact pullback.condition)
  have he₁ : e ≫ pullback.fst j g = pullback.fst j (p ≫ g) :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd j g = pullback.snd j (p ≫ g) ≫ p :=
    pullback.lift_snd _ _ _
  have H : IsPullback e (pullback.snd j (p ≫ g)) (pullback.snd j g) p := by
    apply IsPullback.of_right _ he₂ (IsPullback.of_hasPullback j g)
    rw [he₁]
    exact IsPullback.of_hasPullback j (p ≫ g)
  let _ : Surjective e := MorphismProperty.of_isPullback H.flip inferInstance
  let _ : IsFinite (pullback.fst j (p ≫ g)) :=
    AffineGenericFlatOpen.projection_isFinite (p ≫ g)
  let _ : UniversallyClosed (e ≫ pullback.fst j g) := by
    rw [he₁]
    infer_instance
  let _ : UniversallyClosed (pullback.fst j g) :=
    UniversallyClosed.of_comp_surjective e (pullback.fst j g)
  let _ : IsProper (pullback.fst j g) := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end FLT.Mazur.QuasiCompactGenericFlatOpen
