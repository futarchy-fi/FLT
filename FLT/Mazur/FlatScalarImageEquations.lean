/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarKernelExtension
public import FLT.Mazur.FlatScalarSchemeBaseChange
public import FLT.Mazur.SchemeScalarImageQuotient

/-!
# Exact equations of the full image under flat scalar extension

The image ideal on the entire geometric pullback is the extension of the
original scalar kernel. This preserves nilpotents and applies to the canonical
local branches, without Noetherian hypotheses or a choice of source component.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FlatScalarImageEquations
open FlatScalarSchemeBaseChange FlatScalarFunctionPushout SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Scheme.{0}) [Algebra R Γ(X, ⊤)] [CompactSpace X] [QuasiSeparatedSpace X]

/-- A scalar vanishes on the whole geometric pullback exactly when its tensor vanishes. -/
theorem scalarMap_eq_zero_iff (s : S) :
    scalarMap (base R S X) s = 0 ↔ algebraMap S (S ⊗[R] Γ(X, ⊤)) s = 0 := by
  rw [← sectionsEquiv_left (square R S X)]
  exact map_eq_zero_iff _ (sectionsEquiv (square R S X)).injective

/-- Flat geometric extension preserves the full equation ideal, not merely its radical. -/
theorem equations_eq_map :
    equations (base R S X) =
      (RingHom.ker (algebraMap R Γ(X, ⊤))).map (algebraMap R S) := by
  rw [← FlatScalarKernelExtension.scalar_kernel_eq Γ(X, ⊤) S]
  ext s
  exact scalarMap_eq_zero_iff R S X s

/-- The exact image contains all and only the original scalar equations after extension. -/
theorem equations_eq_original_map :
    equations (base R S X) =
      (equations (SchemeScalarPrincipalNeighborhood.scalarMorphism
        (algebraMap R Γ(X, ⊤)))).map (algebraMap R S) := by
  simp only [equations, scalarMap_scalarMorphism]
  exact equations_eq_map R S X

end FLT.Mazur.FlatScalarImageEquations
