import CoherenceCalculusMathlibBridge.AbstractHilbert

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

theorem AbstractLateShellModel.blockDerivatives_exact
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    continuous_block_derivatives model.blockDerivatives = model.blockDerivatives := by
  rfl

theorem AbstractLateShellModel.effectiveFlow_exact
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    continuous_effective_flow model.effectiveFlow = model.effectiveFlow := by
  rfl

theorem AbstractLateShellModel.toLateShellContract_interpolation
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    model.toLateShellContract.interpolation = model.interpolation := by
  rfl

theorem AbstractLateShellModel.toLateShellContract_blockDerivatives
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    model.toLateShellContract.blockDerivatives = model.blockDerivatives := by
  rfl

theorem AbstractLateShellModel.toLateShellContract_effectiveFlow
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    model.toLateShellContract.effectiveFlow = model.effectiveFlow := by
  rfl

theorem AbstractLateShellModel.toLateShellContract_flowVsTower
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    model.toLateShellContract.flowVsTower = model.flowVsTower := by
  rfl

end CoherenceCalculusMathlibBridge
