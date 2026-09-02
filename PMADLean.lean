-- PMADLean.lean : Master Build Target and Library Orchestration Module
-- Consolidates all verified sub-modules of Phase-Mediated Attractor Dynamics

import PMADLean.Axioms
import PMADLean.Dynamics
import PMADLean.Metrics
import PMADLean.Probability
import PMADLean.Renormalization
import PMADLean.Vorticity
import PMADLean.Incompleteness
import PMADLean.Test
import PMADLean.PhyslibBridge

/--
  The PMADLean root namespace serves as the centralized entry point 
  for the machine-checked mathematical framework accompanying the manuscript:
  "Phase-Mediated Attractor Dynamics: Emergent Spacetime Geometry, the Born Rule, and Universal Attractor Signatures in Driven Many-Body Systems"

  This library formally certifies the logical necessity of compliance floor regularizations,
  attractor dimensionality bounds, and phase-vorticity tensor anti-symmetries, 
  proving that when least-squares optimization filters are bypassed, 
  pristine arrival time manifolds are structurally non-singular and topologically closed.
-/
def PMADLean.version : String := "1.0.0"

