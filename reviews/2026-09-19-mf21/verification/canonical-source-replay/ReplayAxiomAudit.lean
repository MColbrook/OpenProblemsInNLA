import MF21.ActualBoundaryDecay
import MF21.ActualBoundaryDeterminant
import MF21.ActualBoundaryError
import MF21.ActualBoundaryExpansion
import MF21.ActualBoundaryPhase
import MF21.ActualBoundarySimplicity
import MF21.ActualBoundarySmooth
import MF21.ActualPhaseIndexing
import MF21.ActualTailAngles
import MF21.ActualTraceObstruction
import MF21.BoundaryBlockForm
import MF21.BoundaryDecay
import MF21.BoundaryDeterminant
import MF21.BoundaryExpansion
import MF21.BoundaryLeadingTerms
import MF21.BoundaryNormalization
import MF21.BoundaryPolynomial
import MF21.BoundaryReality
import MF21.BoundarySpectrum
import MF21.BulkDecay
import MF21.BulkEndpoint
import MF21.BulkEta
import MF21.BulkImplicit
import MF21.BulkLeadingPhase
import MF21.BulkPhase
import MF21.BulkRootFamily
import MF21.BulkRoots
import MF21.BulkSlopes
import MF21.BulkSymbol
import MF21.BulkTotalPhase
import MF21.CirculantOrdering
import MF21.CirculantSpectrum
import MF21.CoefficientUniqueness
import MF21.CompressionInterlacing
import MF21.Definitions
import MF21.DeterminantSimpleKernel
import MF21.DiscretePowerLimits
import MF21.Eigenangles
import MF21.ExpansionEstimates
import MF21.ExponentialCutoff
import MF21.ExponentialSums
import MF21.FinalTarget
import MF21.FiniteHeadModel
import MF21.FiniteTraceObstruction
import MF21.FirstColumnAsymptotics
import MF21.FirstInverseColumn
import MF21.FourierCoefficients
import MF21.InverseTraceRecurrence
import MF21.LaurentSymbol
import MF21.LogSquaredMesh
import MF21.MF21CoefficientUniqueness
import MF21.MF21TraceSeries
import MF21.MF21Transcendence
import MF21.MF21Transcendence.ETranscendental
import MF21.MF21Transcendence.HermiteLindemann
import MF21.MF21Transcendence.MonicRootSums
import MF21.MF21Transcendence.PiLindemann
import MF21.MF21Transcendence.PiTranscendental
import MF21.MF21Transcendence.SubsetSumEsymm
import MF21.PerturbedPhase
import MF21.PhaseCellRoot
import MF21.PhaseCutoffs
import MF21.PhaseErrorEstimate
import MF21.PhaseIndexing
import MF21.PhaseRotatedError
import MF21.QuantizationTaylor
import MF21.RealBoundaryError
import MF21.RecurrenceBasis
import MF21.SmoothQuantization
import MF21.SpectralBounds
import MF21.SpectralSimplicity
import MF21.SpectralTrace
import MF21.SymbolTransfer
import MF21.ToeplitzGram
import MF21.ToeplitzTraceLimit
import MF21.TopDownIndexing
import MF21.TraceArithmetic
import MF21.TraceIntegralConstant
import MF21.TraceLimitSummation
import MF21.UniformQuantization
import MF21.UniformTaylor
import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
open Lean Elab Command
elab "audit_local_axioms" : command => do
  let wanted : Array String := #["MF21.ActualBoundaryDecay", "MF21.ActualBoundaryDeterminant", "MF21.ActualBoundaryError", "MF21.ActualBoundaryExpansion", "MF21.ActualBoundaryPhase", "MF21.ActualBoundarySimplicity", "MF21.ActualBoundarySmooth", "MF21.ActualPhaseIndexing", "MF21.ActualTailAngles", "MF21.ActualTraceObstruction", "MF21.BoundaryBlockForm", "MF21.BoundaryDecay", "MF21.BoundaryDeterminant", "MF21.BoundaryExpansion", "MF21.BoundaryLeadingTerms", "MF21.BoundaryNormalization", "MF21.BoundaryPolynomial", "MF21.BoundaryReality", "MF21.BoundarySpectrum", "MF21.BulkDecay", "MF21.BulkEndpoint", "MF21.BulkEta", "MF21.BulkImplicit", "MF21.BulkLeadingPhase", "MF21.BulkPhase", "MF21.BulkRootFamily", "MF21.BulkRoots", "MF21.BulkSlopes", "MF21.BulkSymbol", "MF21.BulkTotalPhase", "MF21.CirculantOrdering", "MF21.CirculantSpectrum", "MF21.CoefficientUniqueness", "MF21.CompressionInterlacing", "MF21.Definitions", "MF21.DeterminantSimpleKernel", "MF21.DiscretePowerLimits", "MF21.Eigenangles", "MF21.ExpansionEstimates", "MF21.ExponentialCutoff", "MF21.ExponentialSums", "MF21.FinalTarget", "MF21.FiniteHeadModel", "MF21.FiniteTraceObstruction", "MF21.FirstColumnAsymptotics", "MF21.FirstInverseColumn", "MF21.FourierCoefficients", "MF21.InverseTraceRecurrence", "MF21.LaurentSymbol", "MF21.LogSquaredMesh", "MF21.MF21CoefficientUniqueness", "MF21.MF21TraceSeries", "MF21.MF21Transcendence", "MF21.MF21Transcendence.ETranscendental", "MF21.MF21Transcendence.HermiteLindemann", "MF21.MF21Transcendence.MonicRootSums", "MF21.MF21Transcendence.PiLindemann", "MF21.MF21Transcendence.PiTranscendental", "MF21.MF21Transcendence.SubsetSumEsymm", "MF21.PerturbedPhase", "MF21.PhaseCellRoot", "MF21.PhaseCutoffs", "MF21.PhaseErrorEstimate", "MF21.PhaseIndexing", "MF21.PhaseRotatedError", "MF21.QuantizationTaylor", "MF21.RealBoundaryError", "MF21.RecurrenceBasis", "MF21.SmoothQuantization", "MF21.SpectralBounds", "MF21.SpectralSimplicity", "MF21.SpectralTrace", "MF21.SymbolTransfer", "MF21.ToeplitzGram", "MF21.ToeplitzTraceLimit", "MF21.TopDownIndexing", "MF21.TraceArithmetic", "MF21.TraceIntegralConstant", "MF21.TraceLimitSummation", "MF21.UniformQuantization", "MF21.UniformTaylor", "Solution"]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if wanted.contains modName.toString then
      let data := env.header.moduleData[i]!
      for name in data.constNames do
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {ax} in {name} from {modName}"
        logInfo m!"REPLAY_AXIOMS {name}: {axioms}"
        count := count + 1
  if count == 0 then throwError "No local declarations found"
  logInfo m!"REPLAY_AUDITED_DECLARATIONS {count}"
audit_local_axioms
