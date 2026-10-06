import RequestProject.VerifiedReceivedCover
import RequestProject.GenusSurfaceMonodromyExt

/-!
For the actual subdivided polygon surface, fixing the standard marked loops
under any group action fixes every loop. Flat boundary sections extend through
the explicitly given collar and inner fan. As a consequence, agreement of two
nonabelian cocycles on the marked loops implies equality of their full monodromy
homomorphisms. The surface is not replaced by an assumed presentation.
The proof also constructs a normalized vertex gauge identifying the two
cocycles on every comparability, suitable for the geometric gluing step.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
