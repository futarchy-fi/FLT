/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSourceIntersection

/-!
# Scheme intersections retaining the translation-base map

For a translation defined on any original test V, prescribing the map to V
makes its intersection with an original Picard section an actual open scheme.
The universal property retains both the Picard class and that base map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V U : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V)) (b : U ⟶ V)
  (s : (relativeFppfSheaf f).obj.obj (op U))

/-- The untranslated section with its specified map to the translation base. -/
def baseMarkedHilbertSection : (relativeFppfSheaf f).obj.obj (op U) :=
  s * (relativeFppfSheaf f).obj.map b.op c

/-- The actual open scheme on which the prescribed translated class is represented. -/
def baseMarkedHilbertIntersection : Over (Spec (.of R)) :=
  unpointedAcyclicDegreeTest f U (baseMarkedHilbertSection f V U c b s) d

/-- The open inclusion in the original test. -/
def baseMarkedHilbertArrow : baseMarkedHilbertIntersection f d V U c b s ⟶ U :=
  unpointedAcyclicDegreeArrow f U (baseMarkedHilbertSection f V U c b s) d

instance baseMarkedHilbertArrow_isOpenImmersion :
    IsOpenImmersion (baseMarkedHilbertArrow f d V U c b s).left :=
  unpointedAcyclicDegreeArrow_isOpenImmersion _ _ _ _

instance baseMarkedHilbertArrow_mono : Mono (baseMarkedHilbertArrow f d V U c b s) :=
  Over.mono_of_mono_left _

/-- The parameter map remembers the prescribed translation-base map. -/
def baseMarkedHilbertParameter :
    baseMarkedHilbertIntersection f d V U c b s ⟶ variableHilbertTest f d V :=
  variableHilbertLift f d V (baseMarkedHilbertArrow f d V U c b s ≫ b)
    (acyclicHilbertPicardOverlapToParameter f d hL U
      (baseMarkedHilbertSection f V U c b s))

@[reassoc]
theorem baseMarkedHilbertParameter_base :
    baseMarkedHilbertParameter f hL d V U c b s ≫ variableHilbertBase f d V =
      baseMarkedHilbertArrow f d V U c b s ≫ b :=
  prod.lift_fst _ _

/-- The original class, not a replacement section, is retained on the intersection. -/
theorem baseMarkedHilbertParameter_class :
    variableHilbertPoint f d hL V c _ (baseMarkedHilbertParameter f hL d V U c b s) =
      (relativeFppfSheaf f).obj.map (baseMarkedHilbertArrow f d V U c b s).op s := by
  rw [baseMarkedHilbertParameter, variableHilbertPoint_lift]
  unfold baseMarkedHilbertIntersection
  rw [acyclicHilbertPicardOverlap_class]
  apply div_eq_iff_eq_mul.mpr
  simp only [baseMarkedHilbertSection, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply, baseMarkedHilbertArrow]
  exact ((relativeFppfSheaf f).obj.map
    (baseMarkedHilbertArrow f d V U c b s).op).hom.map_mul _ _

/-- Equal classes and equal base maps factor uniquely through this actual open scheme. -/
theorem baseMarkedHilbertIntersection_lift {W : Over (Spec (.of R))}
    (a : W ⟶ U) (k : W ⟶ variableHilbertTest f d V)
    (hb : k ≫ variableHilbertBase f d V = a ≫ b)
    (hc : variableHilbertPoint f d hL V c W k = (relativeFppfSheaf f).obj.map a.op s) :
    ∃! q : W ⟶ baseMarkedHilbertIntersection f d V U c b s,
      q ≫ baseMarkedHilbertArrow f d V U c b s = a ∧
        q ≫ baseMarkedHilbertParameter f hL d V U c b s = k := by
  have he : acyclicHilbertPicardPoint f d hL W (k ≫ variableHilbertParameter f d V) =
      (relativeFppfSheaf f).obj.map a.op (baseMarkedHilbertSection f V U c b s) := by
    have hh := div_eq_iff_eq_mul.mp hc
    change acyclicHilbertPicardPoint f d hL W (k ≫ variableHilbertParameter f d V) =
      (relativeFppfSheaf f).obj.map a.op s *
        (relativeFppfSheaf f).obj.map (k ≫ variableHilbertBase f d V).op c at hh
    rw [hb] at hh
    simpa only [baseMarkedHilbertSection, map_mul, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hh
  obtain ⟨q, hq, _⟩ := acyclicHilbertPicardOverlap_lift f d hL U
    (baseMarkedHilbertSection f V U c b s) a (k ≫ variableHilbertParameter f d V) he
  have ha : q ≫ baseMarkedHilbertArrow f d V U c b s = a := hq.1
  have hk : q ≫ baseMarkedHilbertParameter f hL d V U c b s = k := by
    apply prod.hom_ext
    · change _ ≫ variableHilbertBase f d V = _
      rw [Category.assoc, baseMarkedHilbertParameter_base, ← Category.assoc, ha]
      exact hb.symm
    · simpa only [baseMarkedHilbertParameter, variableHilbertLift,
        variableHilbertParameter, Category.assoc, prod.lift_snd] using hq.2
  exact ⟨q, ⟨ha, hk⟩, fun r hr ↦
    (cancel_mono (baseMarkedHilbertArrow f d V U c b s)).mp (hr.1.trans ha.symm)⟩

end FLT.Mazur.HilbertChart
