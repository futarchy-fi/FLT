/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSourceCurve
public import FLT.Mazur.RelativeCyclicSubgroupComparison
public import FLT.Mazur.UniversalWeierstrassCyclicModularRepresentation

/-!
# Genuine modular data from the original full marked source families

The smooth chart relation preserves the full generalized curve and the actual
Cartier cyclic subgroup. Thus its classes map to the intended modular classes.
Surjectivity onto arbitrary modular objects is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- The source curve is smooth as a morphism, in addition to its dimension statement. -/
instance cyclicSourceCurve_smoothMorphism : Smooth (cyclicSourceCurve n f).curve.hom :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The actual cyclic source subgroup is ample in its smooth integral curve. -/
theorem cyclicSourceSubgroup_isAmple : (cyclicSourceSubgroup n f).IsAmple :=
  (cyclicSourceSubgroup n f).isAmple_of_smooth (NeZero.pos n)
    (cyclicSourceSubgroup_cartier n f).2.1.1

/-- Original source data define an object of the intended ample cyclic moduli problem. -/
def cyclicSourceLevel : ampleCyclicLevels T n :=
  ⟨⟨cyclicSourceCurve n f, cyclicSourceSubgroup n f⟩,
    (cyclicSourceSubgroup_cartier n f).isCyclic _, cyclicSourceSubgroup_isAmple n f⟩

/-- The modular class of the actual full source curve and its Cartier subgroup. -/
def cyclicSourceModuliClass : ampleCyclicClasses T n :=
  Quotient.mk _ (cyclicSourceLevel n f)

variable (e : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
  auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g))

/-- The actual group comparison extends across the whole original smooth source curves. -/
def cyclicSourceCurveIso : cyclicSourceCurve n f ≅ cyclicSourceCurve n g := by
  let d : (cyclicSourceCurve n f).group ≅ (cyclicSourceCurve n g).group :=
    (CommGrp.forget (Over T)).mapIso e
  let _ : IsMonHom d.hom := inferInstanceAs (IsMonHom e.hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ d

/-- Every original full marked comparison preserves the actual cyclic Cartier subgroup. -/
def cyclicSourceCompatibleIso
    (h : ∀ c, cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom =
      cyclicSchemeOriginalMarking n g c) :
    CompatibleIso (cyclicSourceSubgroup n f) (cyclicSourceSubgroup n g) :=
  relativeCyclicSubgroupCompatibleIso (cyclicSourceMarking n f) (cyclicSourceMarking n g)
    (cyclicSourceMarking_distinct n f) (cyclicSourceMarking_distinct n g)
    (cyclicSourceCurveIso n f g e) (fun i ↦ h (1, i))

/-- The genuine full chart-family relation implies equality in the intended moduli problem. -/
theorem cyclicSourceModuliClass_eq_of_related (h : CyclicMarkedFamilyRelated n f g) :
    cyclicSourceModuliClass n f = cyclicSourceModuliClass n g := by
  obtain ⟨e, he⟩ := h
  exact Quotient.sound ⟨cyclicSourceCompatibleIso n f g e he⟩

/-- Forget full labels after passing to the genuine full chart-family quotient. -/
def cyclicMarkedFamilyClassesToModuli : CyclicMarkedFamilyClasses n T → ampleCyclicClasses T n :=
  Quotient.lift (cyclicSourceModuliClass n)
    (fun f g h ↦ cyclicSourceModuliClass_eq_of_related n f g h)

/-- The class map retains the actual original curve and cyclic Cartier subgroup. -/
theorem cyclicMarkedFamilyClassesToModuli_mk :
    cyclicMarkedFamilyClassesToModuli n (Quotient.mk _ f) = cyclicSourceModuliClass n f := rfl

end FLT.Mazur.UniversalWeierstrass
