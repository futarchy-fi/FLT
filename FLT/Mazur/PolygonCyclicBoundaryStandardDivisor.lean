/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardTranslation

/-!
# Full boundary divisors on the chosen standard extension-field polygon

The specified standard comparison transports the original marking ideals and
their full cyclic product, preserving collisions and canonical line sections.
The same finite relabeling fixes the resulting divisor on the chosen polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction FCurve CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonParameterTranslation.translationIso
  PolygonMarkingBaseChange.markingIdeal PolygonParameterTranslation.movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n) (a : Kˣ) (i : Fin m)
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

/-- The entire original marked ideal on the independently chosen extension-field polygon. -/
def standardLabelIdeal (j : Multiplicative (ZMod n)) :
    (PolygonAtlas.polygon L m).left.IdealSheafData :=
  (labelIdeal K m hm (p) (q) (h) n (g) f a i j).comap (e).hom.left

/-- Each transported factor is relative Cartier over the extension field. -/
theorem standardLabelIdeal_cartier (j : Multiplicative (ZMod n)) :
    RelativeEffectiveCartier (PolygonAtlas.polygon L m).hom
      (standardLabelIdeal K L m hm n f a i j) := by
  let v := (Over.forget (Spec (.of L))).mapIso (e)
  have hs := labelIdeal_cartier K m hm (p) (q) (h) n (g) f a i j
  have hc := hs.comap_of_isOpenImmersion v.hom
  change RelativeEffectiveCartier ((e).hom.left ≫ _)
    (standardLabelIdeal K L m hm n f a i j) at hc
  rw [Over.w] at hc
  exact hc

/-- The product of the full labeled ideals, including coincident factors. -/
def standardOrbitIdeal : (PolygonAtlas.polygon L m).left.IdealSheafData :=
  ∏ j, standardLabelIdeal K L m hm n f a i j

/-- The standard comparison retains the entire original cyclic divisor with multiplicities. -/
theorem standardOrbitIdeal_eq :
    standardOrbitIdeal K L m hm n f a i =
      (orbitIdeal K m hm (p) (q) (h) n (g) f a i).comap (e).hom.left := by
  simp only [standardOrbitIdeal, orbitIdeal, idealSheaf_comap_prod,
    standardLabelIdeal]

/-- The full transported orbit remains relative Cartier. -/
theorem standardOrbitIdeal_cartier :
    RelativeEffectiveCartier (PolygonAtlas.polygon L m).hom
      (standardOrbitIdeal K L m hm n f a i) :=
  relativeEffectiveCartier_prod _ Finset.univ _ fun j _ ↦
    standardLabelIdeal_cartier K L m hm n f a i j

/-- Common relabeling retains the full actual ideal on the chosen extension-field polygon. -/
theorem standardOrbitIdeal_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    standardOrbitIdeal K L m hm n (f ≫ (action (G K m) n r).hom) a i =
      standardOrbitIdeal K L m hm n f a i := by
  rw [standardOrbitIdeal_eq, standardOrbitIdeal_eq, orbitIdeal_action]

/-- The specified standard comparison retains the original positive orbit line. -/
irreducible_def standardOrbitLineComparison :
    (Scheme.Modules.pullback (e).hom.left).obj
      (orbitLine K m hm (p) (q) (h) n (g) f a i) ≅
      divisorLineBundle (standardOrbitIdeal K L m hm n f a i)
        (standardOrbitIdeal_cartier K L m hm n f a i).1 := by
  let hs := (orbitIdeal_cartier K m hm (p) (q) (h) n (g) f a i).1
  let ht := (standardOrbitIdeal_cartier K L m hm n f a i).1
  let he := (standardOrbitIdeal_eq K L m hm n f a i).symm
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The standard comparison preserves the full orbit's canonical vanishing section. -/
theorem standardOrbitLineComparison_section :
    DivisorLineSectionCompatible (e).hom.left
      (orbitIdeal_cartier K m hm (p) (q) (h) n (g) f a i).1
      (standardOrbitIdeal_cartier K L m hm n f a i).1
      (standardOrbitLineComparison K L m hm n f a i) := by
  let hs := (orbitIdeal_cartier K m hm (p) (q) (h) n (g) f a i).1
  let ht := (standardOrbitIdeal_cartier K L m hm n f a i).1
  let he := (standardOrbitIdeal_eq K L m hm n f a i).symm
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [standardOrbitLineComparison_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonCyclicBoundary
