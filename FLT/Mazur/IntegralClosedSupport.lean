/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSupport
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Integral closed supports

The vanishing ideal of a closed subset defines its reduced induced subscheme.
For an irreducible closed subset this scheme is integral, and its generic point
maps to the generic point of the given subset. Applying this construction to
closed coherent support requires no choice of a subscheme or generic point.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- The reduced induced scheme structure on a closed subset. -/
def reducedClosedSubscheme (Z : Closeds X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal Z).subscheme

/-- The inclusion of the reduced induced closed subscheme. -/
def reducedClosedSubschemeι (Z : Closeds X) : reducedClosedSubscheme Z ⟶ X :=
  (IdealSheafData.vanishingIdeal Z).subschemeι

instance integralClosedSupportInst1 (Z : Closeds X) :
    IsClosedImmersion (reducedClosedSubschemeι Z) :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal Z).subschemeι)

@[simp]
lemma range_reducedClosedSubschemeι (Z : Closeds X) :
    Set.range (reducedClosedSubschemeι Z) = Z :=
  IdealSheafData.range_subschemeι _

/-- The defining ideal is precisely the vanishing ideal of the original closed subset. -/
@[simp]
lemma ker_reducedClosedSubschemeι (Z : Closeds X) :
    (reducedClosedSubschemeι Z).ker = IdealSheafData.vanishingIdeal Z :=
  IdealSheafData.ker_subschemeι _

/-- The affine charts of the induced subscheme have reduced quotient rings. -/
instance reducedClosedSubscheme_isReduced (Z : Closeds X) :
    IsReduced (reducedClosedSubscheme Z) := by
  let I := IdealSheafData.vanishingIdeal Z
  apply (IsReduced.iff_of_openCover _ I.subschemeCover.openCover).mpr
  intro U
  apply (affine_isReduced_iff _).mpr
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- Irreducibility of the closed subset gives integrality of its induced scheme. -/
theorem reducedClosedSubscheme_isIntegral (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (reducedClosedSubscheme Z) := by
  have : IrreducibleSpace (reducedClosedSubscheme Z) := Subtype.irreducibleSpace hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The generic point, constructed inside the reduced closed subscheme. -/
def closedSubschemeGenericPoint (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    reducedClosedSubscheme Z := by
  have : IrreducibleSpace (reducedClosedSubscheme Z) := Subtype.irreducibleSpace hZ
  exact genericPoint (reducedClosedSubscheme Z)

lemma closedSubschemeGenericPoint_spec (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsGenericPoint (closedSubschemeGenericPoint Z hZ) Set.univ := by
  have : IrreducibleSpace (reducedClosedSubscheme Z) := Subtype.irreducibleSpace hZ
  exact genericPoint_spec _

/-- The constructed point maps to a generic point of exactly the prescribed closed subset. -/
theorem image_closedSubschemeGenericPoint_spec (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IsGenericPoint (reducedClosedSubschemeι Z (closedSubschemeGenericPoint Z hZ))
      (Z : Set X) := by
  have h := (closedSubschemeGenericPoint_spec Z hZ).image
    (reducedClosedSubschemeι Z).continuous
  simpa only [Set.image_univ, range_reducedClosedSubschemeι, Z.isClosed.closure_eq] using h

/-- This agrees with the generic point obtained from sobriety of the ambient scheme. -/
theorem image_closedSubschemeGenericPoint (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    reducedClosedSubschemeι Z (closedSubschemeGenericPoint Z hZ) = hZ.genericPoint :=
  (image_closedSubschemeGenericPoint_spec Z hZ).eq (hZ.isGenericPoint_genericPoint Z.isClosed)

/-- A closed subset contains the generic point precisely when it contains all of the support. -/
lemma closedSubschemeGenericPoint_mem_closed_iff (Z W : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    reducedClosedSubschemeι Z (closedSubschemeGenericPoint Z hZ) ∈ W ↔ Z ≤ W :=
  (image_closedSubschemeGenericPoint_spec Z hZ).mem_closed_set_iff W.isClosed

/-- The actual closed support of a coherent sheaf carries a canonical reduced scheme structure. -/
def supportSubscheme (M : X.Modules) [M.IsFinitePresentation] : Scheme.{u} :=
  reducedClosedSubscheme (closedSupport M)

/-- Its inclusion into the ambient scheme. -/
def supportSubschemeι (M : X.Modules) [M.IsFinitePresentation] : supportSubscheme M ⟶ X :=
  reducedClosedSubschemeι (closedSupport M)

instance integralClosedSupportInst2 (M : X.Modules) [M.IsFinitePresentation] :
    IsClosedImmersion (supportSubschemeι M) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedSubschemeι (closedSupport M)))

instance integralClosedSupportInst3 (M : X.Modules) [M.IsFinitePresentation] :
    IsReduced (supportSubscheme M) :=
  inferInstanceAs (IsReduced (reducedClosedSubscheme (closedSupport M)))

@[simp]
lemma range_supportSubschemeι (M : X.Modules) [M.IsFinitePresentation] :
    Set.range (supportSubschemeι M) = support M :=
  range_reducedClosedSubschemeι _

/-- Irreducible coherent support gives an integral closed subscheme without additional data. -/
theorem supportSubscheme_isIntegral (M : X.Modules) [M.IsFinitePresentation]
    (hM : IsIrreducible (support M)) : IsIntegral (supportSubscheme M) :=
  reducedClosedSubscheme_isIntegral (closedSupport M) hM

end FLT.Mazur.FCurve.CoherentDevissage
