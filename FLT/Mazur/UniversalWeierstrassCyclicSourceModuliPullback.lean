/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuli
public import FLT.Mazur.RelativeCyclicSubgroupPullbackComparison
public import FLT.Mazur.OverPullbackSectionMonoidal

/-!
# Actual modular source data commute with base change

The original group-family comparison extends to the full smooth curves and
identifies the actual Cartier subgroups, retaining their component generators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The full original smooth source curve compares with the actual pulled-back curve. -/
def cyclicSourceCurvePullbackIso :
    cyclicSourceCurve n (k ≫ f) ≅ (cyclicSourceCurve n f).baseChange k := by
  let _ : Smooth ((cyclicSourceCurve n f).baseChange k).curve.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd (cyclicSourceCurve n f).curve.hom k)
    infer_instance
  let e : (cyclicSourceCurve n (k ≫ f)).group ≅ ((cyclicSourceCurve n f).baseChange k).group :=
    (CommGrp.forget (Over U)).mapIso (cyclicSourceOriginalGroupIso n f k).symm
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (cyclicSourceOriginalGroupIso n f k).inv.hom.hom.hom)
  exact isoOfSmoothGroup _ _ e

/-- Each original cyclic section is the monoidal pullback of the original section. -/
theorem cyclicSourceCurvePullbackIso_marking (i : Multiplicative (ZMod n)) :
    cyclicSourceMarking n (k ≫ f) i ≫ (cyclicSourceCurvePullbackIso n f k).hom.group =
      Functor.LaxMonoidal.ε (Over.pullback k) ≫
        (Over.pullback k).map (cyclicSourceMarking n f i) := by
  let e : (Over.pullback k).obj (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X ≅
      (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (k ≫ f))).X :=
    (CommGrp.forget (Over U)).mapIso (cyclicSourceOriginalGroupIso n f k)
  change cyclicSchemeOriginalMarking n (k ≫ f) (1, i) ≫ e.inv = _
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [OverPullbackSection.monoidal_section_eq_lift k _
    (cyclicSourceMarking n f i) (cyclicSourceOriginalSection n f k (1, i)) rfl]
  exact (cyclicSourceOriginalGroupIso_marking n f k (1, i)).symm

/-- Both the original source curve and its Cartier subgroup compare with actual base change. -/
def cyclicSourceSubgroupPullbackIso :
    CompatibleIso (cyclicSourceSubgroup n (k ≫ f)) ((cyclicSourceSubgroup n f).baseChange k) :=
  relativeCyclicSubgroupPullbackCompatibleIso k (cyclicSourceMarking n f)
    (cyclicSourceMarking n (k ≫ f)) (cyclicSourceMarking_distinct n f)
    (cyclicSourceMarking_distinct n (k ≫ f)) (cyclicSourceCurvePullbackIso n f k)
    (cyclicSourceCurvePullbackIso_marking n f k)

/-- The original source modular class commutes with arbitrary source change. -/
theorem cyclicSourceModuliClass_pullback :
    cyclicSourceModuliClass n (k ≫ f) =
      ampleCyclicClassesPullback k n (cyclicSourceModuliClass n f) :=
  Quotient.sound ⟨cyclicSourceSubgroupPullbackIso n f k⟩

/-- The chart-family class map into the actual modular classes is natural. -/
theorem cyclicMarkedFamilyClassesToModuli_natural (q : CyclicMarkedFamilyClasses n T) :
    cyclicMarkedFamilyClassesToModuli n (cyclicMarkedFamilyClassesPullback n k q) =
      ampleCyclicClassesPullback k n (cyclicMarkedFamilyClassesToModuli n q) := by
  induction q using Quotient.inductionOn with
  | h f => exact cyclicSourceModuliClass_pullback n f k

end FLT.Mazur.UniversalWeierstrass
