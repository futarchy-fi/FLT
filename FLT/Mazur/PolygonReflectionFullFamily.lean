/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonReflectionAction
public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.GeneralizedCurveCategory
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Reflection on the original polygon smooth locus

The whole reducible polygon reflection restricts to inversion of its actual
smooth group. The comparison retains the normalization map and each torus chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory GrpObj
namespace FLT.Mazur.PolygonGeneralizedCurve
open PolygonPinching PolygonActionSmooth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Reflection of the original smooth inclusion is inversion on every component. -/
@[reassoc] theorem inclusion_reflection :
    (curve K n hn p q h).inclusion ≫ polygonReflection K hn p q h =
      PolygonSplitGroup.inversion K n ≫ (curve K n hn p q h).inclusion := by
  let _ := polygon_lfp K n hn p q h
  change smoothMap K n hn p q h ≫ polygonReflection K hn p q h =
    PolygonSplitGroup.inversion K n ≫ smoothMap K n hn p q h
  apply Sigma.hom_ext
  intro i
  change PolygonSplitGroup.component K n i ≫ _ =
    PolygonSplitGroup.component K n i ≫ _
  rw [component_smoothMap_assoc, componentι_polygonReflection,
    ProjectiveLine.torus_endpointReversal_assoc,
    PolygonSplitGroup.component_inversion_assoc, component_smoothMap]
  simp only [reflectIndex, RingEquiv.apply_symm_apply]

end FLT.Mazur.PolygonGeneralizedCurve

/-!
# Reflection of the full generalized polygon family

The actual whole-curve reflection, smooth-group inversion and equivariance
assemble into a full DR automorphism. Its square is the identity on the entire
reducible polygon, including its nodes, group and action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonGeneralizedCurve
open PolygonPinching GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Reflection preserves the original group and its action on the whole polygon. -/
def reflection : curve K n hn p q h ⟶ curve K n hn p q h where
  curve := polygonReflection K hn p q h
  group := PolygonSplitGroup.inversion K n
  isMonHom := inferInstanceAs (IsMonHom ι[PolygonSplitGroup.model K n])
  inclusion := inclusion_reflection K n hn p q h
  action := polygonAction_reflection K hn p q h

/-- The full generalized-curve reflection satisfies the original involution relation. -/
@[reassoc] theorem reflection_involutive :
    reflection K n hn p q h ≫ reflection K n hn p q h = 𝟙 (curve K n hn p q h) := by
  apply (forgetCurve (S := Spec (.of K))).map_injective
  exact polygonReflection_involutive K hn p q h

/-- The full pointed boundary family is unchanged by its original reflection. -/
def reflectionIso : curve K n hn p q h ≅ curve K n hn p q h where
  hom := reflection K n hn p q h
  inv := reflection K n hn p q h
  hom_inv_id := reflection_involutive K n hn p q h
  inv_hom_id := reflection_involutive K n hn p q h

/-- The full comparison keeps precisely the original marked reflection on the curve. -/
theorem reflectionIso_curve :
    (reflectionIso K n hn p q h).hom.curve = polygonReflection K hn p q h := rfl

/-- The full comparison restricts precisely to inversion on the smooth group. -/
theorem reflectionIso_group :
    (reflectionIso K n hn p q h).hom.group = ι[(curve K n hn p q h).group] := rfl

/-- In particular, the original identity section is retained on the reducible boundary. -/
@[reassoc] theorem identitySection_reflection :
    (curve K n hn p q h).identitySection ≫ polygonReflection K hn p q h =
      (curve K n hn p q h).identitySection :=
  (reflection K n hn p q h).identitySection

end FLT.Mazur.PolygonGeneralizedCurve

/-!
# Reflection retains every original polygon finite subgroup

Inversion of the original subgroup carrier gives a compatible comparison
with the whole-curve reflection. This applies also to non-etale subgroups:
the carrier and its Cartier multiplicities remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonGeneralizedCurve
open PolygonPinching GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {d : ℕ} (H : (curve K n hn p q h).FiniteSubgroup d)

/-- The original finite subgroup is preserved by full-family boundary reflection. -/
def reflectionSubgroupIso : FiniteSubgroup.CompatibleIso H H where
  curve := reflectionIso K n hn p q h
  subgroup :=
    { hom := ι[H.carrier]
      inv := ι[H.carrier]
      hom_inv_id := inv_comp_inv H.carrier
      inv_hom_id := inv_comp_inv H.carrier }
  isMonHom := inferInstanceAs (IsMonHom ι[H.carrier])
  compatible := by
    change (H.inclusion ≫ (curve K n hn p q h).inclusion) ≫
      (reflection K n hn p q h).curve = _
    rw [Category.assoc, (reflection K n hn p q h).inclusion]
    change H.inclusion ≫ ι[(curve K n hn p q h).group] ≫
      (curve K n hn p q h).inclusion =
        ι[H.carrier] ≫ H.inclusion ≫ (curve K n hn p q h).inclusion
    rw [← Category.assoc, ← inv_hom, Category.assoc]

/-- Each original Cartier generator is carried to its inverse on the same subgroup. -/
theorem reflection_cartierGenerator {P : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) : H.IsCartierGenerator P⁻¹ :=
  (reflectionSubgroupIso K n hn p q h H).cartierGenerator hP

end FLT.Mazur.PolygonGeneralizedCurve
