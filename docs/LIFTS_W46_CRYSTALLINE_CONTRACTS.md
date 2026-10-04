# Lp0: integral crystalline input contracts

These are mathematical implementation contracts, not Lean declarations or
assumptions added to a lifting record. None of the comparison theorems below
has been implemented. `CofinalFlatModels` proves a cofinal finite-flat reduction
criterion; it does not construct crystalline periods or a Barsotti–Tate model.

## Scope and conventions

Fix a prime p, a finite extension E/Q_p with valuation ring O and uniformizer
pi, and a free rank-two O-lattice T with continuous G_Qp action. The local field
is Q_p; extending the scope to ramified local fields needs a separate contract.
Use the covariant Tate module convention: Q_p(1) has Hodge–Tate weight -1.
Thus the weight-two modular representation has weights {0,-1} here, and its
dual has weights {0,1}. Any interface using {0,1} must take the dual explicitly.
Crystallinity is a property of V = T tensor_O E, not of a residual module.

## C0: period objects and the crystalline predicate

Construct B_cris, B_dR and their G_Qp actions, Frobenius on B_cris, the comparison
map B_cris -> B_dR, and the filtration on B_dR. Define D_cris(V) as invariants
of B_cris tensor_Qp V, with the commuting E-action. Define crystallinity by
invertibility of the natural period comparison map; prove the dimension
criterion from it. Define Hodge–Tate weights using the associated graded of
D_dR(V), with the convention above. A boolean predicate named `IsCrystalline`
with no period construction is not this deliverable.

Done: the two rank-one examples E and E(1), including filtrations, dimensions,
and comparison maps, are proved from the definitions. Required naturality:
restriction of scalars in E, finite extension of E, duals, tensor products,
and the actual cyclotomic character already used by the representation API.

## C1: integral Barsotti–Tate object

Use or extend the existing p-divisible/finite-flat group-scheme objects over
Z_p. Construct the finite levels G[p^n], their transition maps, and their
geometric generic fibres. The O-action must be an action on the group scheme,
not just on its generic points. Its Tate module is the inverse limit of these
actual point modules, with its continuous Galois action and O-module structure.
The underlying p-divisible group has height 2[E:Q_p] for an O-rank-two Tate
module; height two is correct only when O=Z_p. The corresponding dimension is
[E:Q_p] for the weights specified above.

Done: prove finite freeness, the rank, the Galois and O-action laws, and the
canonical level comparison T_p(G)/p^n -> G[p^n](Qpbar). For ramified O, the
pi-power levels must be constructed and proved finite flat; they cannot be
identified with the p-power levels by changing notation.

## C2: crystalline lattice to an integral model

Input: the continuous lattice T, the constructed crystalline comparison for V,
and the proved weight condition. Output: a p-divisible group G/Z_p with O-action
and an O-linear, continuous G_Qp-equivariant isomorphism T_p(G) ≃ T.
The integral isomorphism is a theorem output. A supplied generic isomorphism
or a record field asserting existence of G would only restate Lp0.

A Fontaine–Laffaille proof for p>2 may first construct strongly divisible
filtered Frobenius modules of weights [0,1] for the dual lattice. It must prove
the integral equivalence and recover the specified lattice, not merely some
lattice in V. This proof route does not cover p=2 without an additional theorem.
A Barsotti–Tate classification proof covering p=2 must state its separate
integral hypotheses and prove them in the intended application.

## C3: model to the existing flatness interface

Starting with C2's actual G and Tate-module comparison, construct finite-flat
models for T/pi^n and prove compatibility of their generic point modules with
the actual coefficient reductions. For p-power levels use C1; for pi-power
levels use the proved O-action kernel construction. Feed these witnesses to
the existing cofinal flatness criterion only after checking its coefficient
ring, topology, and reduction-index conventions.

Done: a theorem from C0's crystalline weight-two property of V and the given
lattice T to the repository's existing local flatness predicate. Its proof
must name C2 and the finite-flat level comparisons in its axiom audit.

## C4: deformation use

For a universal deformation, specify which arithmetic local property is being
imposed: finite flatness at finite coefficient levels, or a characteristic-zero
crystalline locus with the fixed weights and determinant. These are different
interfaces; their equivalence/effectivity is a theorem, not a definition.
Prove base change and compatible-limit behavior before identifying a closed
ideal in the universal deformation ring. W45's closed-sum construction applies
after those individual ideal classifications exist.

Implementation order: C0 rank-one examples; C1 finite levels and Tate comparison;
C2 integral classification with its p=2 scope explicit; C3 bridge to flatness;
C4 arithmetic deformation ideal. No period or classification API is assumed
available by this plan.
