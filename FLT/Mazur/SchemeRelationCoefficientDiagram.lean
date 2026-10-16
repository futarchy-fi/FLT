/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBaseSectionAlgebra
public import FLT.Mazur.FlatAlgebraEqualizerNaturality

/-!
# The coefficient diagram of a map of full scheme relations

Actual morphisms over the coefficient base give commuting algebra maps on
source and relation sections. Flat tensor equalizer comparison respects these
maps. No affine quotient, finite invariant generators, or effectivity is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationCoefficientDiagram
open Approximation FlatAlgebraEqualizer
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]
  {A D A' D' : Over (Spec (.of R))}

/-- Global sections retain the algebra of the original structural morphism. -/
local instance sectionAlgebra (Y : Over (Spec (.of R))) : Algebra R Γ(Y.left, ⊤) :=
  affineBaseSectionAlgebra Y.hom

/-- The structural-base-linear pullback of actual source or relation sections. -/
def sectionMap {Y Z : Over (Spec (.of R))} (a : Y ⟶ Z) :
    Γ(Z.left, ⊤) →ₐ[R] Γ(Y.left, ⊤) :=
  affineBaseSectionHom Y.hom Z.hom a.left a.w

variable (p q : D ⟶ A) (p' q' : D' ⟶ A') (i : A' ⟶ A) (z : D' ⟶ D)
  (hp : z ≫ p = p' ≫ i) (hq : z ≫ q = q' ≫ i)

include hp in
/-- A whole geometric endpoint square gives the exact original coefficient square. -/
theorem endpoint_square :
    (sectionMap p').comp (sectionMap i) = (sectionMap z).comp (sectionMap p) := by
  ext a
  change p'.left.appTop (i.left.appTop a) = z.left.appTop (p.left.appTop a)
  have h := congrArg (fun b ↦ b.left.appTop a) hp
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using h.symm

/-- The complete original invariant algebra of a two-endpoint scheme relation. -/
def invariants : Subalgebra R Γ(A.left, ⊤) :=
  AlgHom.equalizer (sectionMap p) (sectionMap q)

/-- Restriction of original invariants is constructed from both geometric endpoint squares. -/
def invariantMap : invariants p q →ₐ[R] invariants p' q' :=
  equalizerMap _ _ _ _ (sectionMap i) (sectionMap z)
    (endpoint_square p p' i z hp) (endpoint_square q q' i z hq)

/-- The invariant restriction has exactly the original source pullback as its value. -/
theorem invariantMap_val (a : invariants p q) :
    (invariantMap p q p' q' i z hp hq a).val = i.left.appTop a.val := rfl

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The full equations after extending the actual original coefficient ground. -/
abbrev tensorInvariants :=
  AlgHom.equalizer (tensorMap S (sectionMap p)) (tensorMap S (sectionMap q))

/-- Boundary restriction between full ground-extended relation equations. -/
def tensorInvariantMap : tensorInvariants p q S →ₐ[S] tensorInvariants p' q' S :=
  tensorEqualizerMap _ _ _ _ (sectionMap i) (sectionMap z)
    (endpoint_square p p' i z hp) (endpoint_square q q' i z hq) S

variable [Module.Flat R S]

/-- The full original invariant algebra commutes with flat extension of the ground ring. -/
def flatComparison : S ⊗[R] invariants p q ≃ₐ[S] tensorInvariants p q S :=
  comparison (sectionMap p) (sectionMap q) S

/-- The flat invariant comparison retains the original source coefficients. -/
theorem flatComparison_tmul (s : S) (a : invariants p q) :
    (flatComparison p q S (s ⊗ₜ[R] a)).val = s ⊗ₜ[R] a.val := rfl

/-- The entire geometric boundary diagram commutes after flat coefficient comparison. -/
theorem flatComparison_natural (a : S ⊗[R] invariants p q) :
    tensorInvariantMap p q p' q' i z hp hq S (flatComparison p q S a) =
      flatComparison p' q' S (tensorMap S (invariantMap p q p' q' i z hp hq) a) :=
  comparison_natural _ _ _ _ (sectionMap i) (sectionMap z)
    (endpoint_square p p' i z hp) (endpoint_square q q' i z hq) S a

end FLT.Mazur.SchemeRelationCoefficientDiagram
