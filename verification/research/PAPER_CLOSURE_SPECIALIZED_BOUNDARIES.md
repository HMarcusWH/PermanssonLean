# E-02 and E-03 concrete negative statements

`Specialized/BoundaryWitnesses.lean` proves that an exact negative approximant
can lie outside the legal carrier, and that an injective identity embedding
can lose negativity when it changes the form. These examples explain the
legality and form-preservation premises of `FiniteDetection`.

The actual Schur complement of a one-dimensional zero core, zero coupling,
two-dimensional shell `diag(-1,0)` and shift `-1` is `diag(0,1)`. Its first
scalar equation holds on `(0,1)`, while its second equation fails. At shift
zero the PSD zero core has no inverse. The original shell theorem retains
the full finite matrix and requires a strictly negative shift.

These are kernel-checked negative theorems. The discovered Lean wrapper
rechecks their source hashes, signatures and transitive axioms. Four separate
exact rational Python checks in `test_paper_closure_boundaries.py` provide
independent arithmetic countermodels. Neither evidence kind is described as
a rejected compiler mutation.
