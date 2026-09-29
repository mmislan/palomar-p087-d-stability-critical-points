# Claim correspondence

| Declaration | Statement | Manuscript |
|---|---|---|
| `DStability5x5.dStable_iff_explicit` | In every dimension, D-stability iff Hurwitz stability and no positive contact satisfying the Fritz-John equations, for arbitrary positive barrier weights | Theorem 3.4 |
| `DStability5x5.dStable_iff_five` | The five-dimensional principal-minor specialization, excluding both the Lagrange and tangency systems | Theorem 3.6 |

`DStable` quantifies over all strictly positive diagonal scalings. `HurwitzStable` requires strictly negative real parts for every complex eigenpair. The matrix is unrestricted; there is no assumed checker, oracle or feasibility certificate. Positive barrier weights exist in every dimension (take both weights identically one). The universal criterion includes dimension zero; the second theorem has dimension exactly five. The nonzero multiplier condition prevents trivial Fritz-John certificates, and the tangency branch retains singular contacts.

The proof combines spectral continuation, the contact determinant, a proper exhaustion of the positive orthant and the Fritz-John condition at an attained minimum. Definitions, lemmas and their project import closure are included under `proofs/`. Companion manuscripts supply context and test families; they are not extra assumptions of the selected statements.

These equivalences are the selected formal contribution. The manuscript also discusses a finite solving procedure, generic finiteness, degree counts, robustness and numerical applications; those claims have their own stated evidence and are not additional Comparator endpoints. In particular, the numerical count 980 is not a Lean theorem.

Johnson's contact criterion and the classical critical-point method are credited in the manuscript. The contribution is their explicit principal-minor formulation and formal proof, including the literal five-dimensional system. The submission does not claim priority for the general critical-point method or for decidability by quantifier elimination.
