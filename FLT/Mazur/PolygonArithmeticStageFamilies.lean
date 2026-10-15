/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport

/-!
# Marked polygon families over the original arithmetic thickenings

The stages over A/(π^(m+1)) are actual Cartesian specializations of the
universal stages with coefficients in A. Every specified unit-one marking
is retained. The construction applies equally in mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

instance parameter_nilpotent : Fact (IsNilpotent (parameter A π m)) :=
  ⟨m + 1, parameter_pow A π m⟩

/-- The marked cyclic family over the actual arithmetic thickening. -/
def family : Over (Spec (.of (Quotient A π m))) :=
  PolygonInfinitesimal.family (Quotient A π m) (parameter A π m) n h

instance family_flat : Flat (family A π m n h).hom :=
  PolygonInfinitesimal.toBase_flat _ _ n h

instance family_locallyOfFinitePresentation : LocallyOfFinitePresentation (family A π m n h).hom :=
  PolygonInfinitesimal.toBase_locallyOfFinitePresentation _ _ n h

instance family_quasiCompact : QuasiCompact (family A π m n h).hom :=
  PolygonInfinitesimal.toBase_quasiCompact _ _ n h

instance family_separated : IsSeparated (family A π m n h).hom :=
  PolygonInfinitesimalSeparated.separated _ _ n h

/-- The original unit-one marking, with its unchanged cyclic index. -/
def marking (i : Fin n) : Spec (.of (Quotient A π m)) ⟶ (family A π m n h).left :=
  PolygonInfinitesimal.marking (Quotient A π m) (parameter A π m) n h i 1

/-- Each original arithmetic marking is a section. -/
@[reassoc] theorem marking_base (i : Fin n) :
    marking A π m n h i ≫ (family A π m n h).hom = 𝟙 _ :=
  PolygonInfinitesimal.marking_base _ _ n h i 1

/-- Distinct labels have disjoint marked sections over every arithmetic thickening. -/
theorem markings_pairwise : Pairwise (fun i j ↦
    Disjoint (Set.range (marking A π m n h i)) (Set.range (marking A π m n h j))) :=
  PolygonInfinitesimal.pairwise_markings _ _ n h (fun _ ↦ 1)

/-- The actual integral coefficient map on spectra. -/
def specializationBase :
    Spec (.of (Quotient A π m)) ⟶ Spec (.of (PolygonInfinitesimalStages.Ring A m)) :=
  Spec.map (CommRingCat.ofHom (specialization A π m).toRingHom)

instance specializationBase_isClosedImmersion : IsClosedImmersion (specializationBase A π m) :=
  IsClosedImmersion.spec_of_surjective _ (specialization_surjective A π m)

/-- The assembled specialization to the original universal polygon. -/
def specializationFamily :
    (family A π m n h).left ⟶ (PolygonInfinitesimalStages.family A m n h).left :=
  PolygonInfinitesimal.parameterProjection (specialization A π m).toRingHom
    (PolygonInfinitesimalStages.parameter A m) (parameter A π m)
    (specialization_parameter A π m) n h

/-- The integral specialization is Cartesian on the entire family. -/
theorem specializationFamily_isPullback :
    IsPullback (specializationFamily A π m n h) (family A π m n h).hom
      (PolygonInfinitesimalStages.family A m n h).hom (specializationBase A π m) :=
  PolygonInfinitesimal.parameterProjection_isPullback _ _ _
    (specialization_parameter A π m) n h

/-- The family projection preserves the original integral coefficient map. -/
@[reassoc] theorem specializationFamily_base :
    specializationFamily A π m n h ≫ (PolygonInfinitesimalStages.family A m n h).hom =
      (family A π m n h).hom ≫ specializationBase A π m :=
  (specializationFamily_isPullback A π m n h).w

/-- The full arithmetic family is the specified universal pullback. -/
def specializationIso : (family A π m n h).left ≅
    pullback (PolygonInfinitesimalStages.family A m n h).hom (specializationBase A π m) :=
  (specializationFamily_isPullback A π m n h).isoPullback

/-- The entire Cartesian comparison retains every original unit-one marking. -/
theorem marking_specializationIso (i : Fin n) :
    marking A π m n h i ≫ (specializationIso A π m n h).hom =
      pullback.lift (specializationBase A π m ≫ PolygonInfinitesimalStages.marking A m n h i)
        (𝟙 _) (by rw [Category.assoc, PolygonInfinitesimalStages.marking_base,
          Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, specializationIso,
      (specializationFamily_isPullback A π m n h).isoPullback_hom_fst, pullback.lift_fst]
    simpa only [map_one, marking, specializationFamily, specializationBase,
      PolygonInfinitesimalStages.marking] using PolygonInfinitesimal.marking_parameterProjection
      (specialization A π m).toRingHom (PolygonInfinitesimalStages.parameter A m)
      (parameter A π m) (specialization_parameter A π m) n h i 1
  · rw [Category.assoc, specializationIso,
      (specializationFamily_isPullback A π m n h).isoPullback_hom_snd,
      pullback.lift_snd, marking_base]

end FLT.Mazur.PolygonArithmeticStages
