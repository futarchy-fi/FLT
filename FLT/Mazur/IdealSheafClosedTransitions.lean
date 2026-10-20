/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Cartesian transitions between unchanged pulled ideal subschemes

An exact ideal pullback constructs the closed subscheme transition, its
cartesian square and its composition law. Section restriction commutes with
this actual scheme map, without passing to reduced closed loci.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.IdealSheafClosedTransitions
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Scheme.{0}} (I : X.IdealSheafData) (J : Y.IdealSheafData)
  (a : X ⟶ Y) (h : J.comap a = I)

/-- The actual boundary transition constructed from exact ideal pullback. -/
def map : I.subscheme ⟶ J.subscheme :=
  I.subschemeMap J a (Scheme.IdealSheafData.le_map_iff_comap_le.mpr h.le)

/-- The closed transition retains the original source morphism. -/
@[reassoc]
theorem map_inclusion : map I J a h ≫ J.subschemeι = I.subschemeι ≫ a :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The constructed transition is the entire closed base change. -/
theorem isPullback : IsPullback I.subschemeι (map I J a h) a J.subschemeι := by
  subst I
  apply IsPullback.of_iso_pullback ⟨(map_inclusion _ _ _ _).symm⟩ (J.comapIso a)
  · exact Scheme.IdealSheafData.comapIso_hom_fst J a
  · exact Scheme.IdealSheafData.comapIso_hom_snd J a

/-- Closed order inclusions induce closed transitions on the full boundary. -/
instance map_closed [IsClosedImmersion a] : IsClosedImmersion (map I J a h) :=
  MorphismProperty.of_isPullback (isPullback I J a h) (inferInstanceAs (IsClosedImmersion a))

/-- Consecutive boundary transitions retain the exact composite scheme map. -/
@[reassoc]
theorem map_comp (K : Z.IdealSheafData) (b : Y ⟶ Z) (hb : K.comap b = J) :
    map I J a h ≫ map J K b hb =
      map I K (a ≫ b) (by rw [Scheme.IdealSheafData.comap_comp, hb, h]) := by
  apply (cancel_mono K.subschemeι).mp
  simp only [Category.assoc, map_inclusion, map_inclusion_assoc]

/-- Restricting an ambient function and then its boundary equals the opposite path. -/
theorem section_square (s : Γ(Y, ⊤)) :
    I.subschemeι.appTop (a.appTop s) = (map I J a h).appTop (J.subschemeι.appTop s) := by
  change (I.subschemeι ≫ a).appTop s = (map I J a h ≫ J.subschemeι).appTop s
  rw [map_inclusion]

/-- Exact boundary lifts stay exact under the nonflat transition. -/
theorem lift_restrict (s : Γ(Y, ⊤)) (t : Γ(J.subscheme, ⊤))
    (hs : J.subschemeι.appTop s = t) :
    I.subschemeι.appTop (a.appTop s) = (map I J a h).appTop t := by
  rw [section_square, hs]

end FLT.Mazur.IdealSheafClosedTransitions
